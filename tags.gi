
##  Copyright (c) 2018-2021, Carnegie Mellon University
##  See LICENSE for details

Declare(simtBlockIdxX, simtBlockIdxY, simtBlockIdxZ);
Declare(simtThreadIdxX, simtThreadIdxY, simtThreadIdxZ);
Declare(simt_syncgrid, simt_syncblock, simt_synccluster);

Declare(ASIMTListDim);

# The basic assumption is that threads are organized in a 6-dimensional structure (a 3D grid of 3D blocks).

# A dimension tag is a list of (thread) ranges over a one or more Grid/Block dimensions.
# e.g., ASIMTGridDimX(32) refers to 32 blocks (indexed from 0 to 31) over the X grid dimension.

# A range can also be a subset of the whole set of allocated elements:
# e.g., ASIMTGridDimX(32, [4,8]) refers to 5 blocks (indexed from 4 to 8) over the X grid dimension.

# More than one ranges can also be expressed over the same dimension:
# e.g., ASIMTGridDimX(32, [0,3], [4,8])
# As well as over different ones:
# e.g., ASIMTListDim( ASIMTGridDimX(32, [4,8]), ASIMTGridDimY(96) )


# SIMT Grid/BLock Dimension tags
Class(ASIMTDim, ASingletonTag, rec(
    isSIMTTag := true,
    # When lowering to icode a dimension tag instantiates a dimension index
    _idx      := Ignore,
    _build_gen_idx := (self, Idx, plist) >> ApplyFunc(Idx, plist),
    simt_idx    := (arg) >> let(self := arg[1], idx := Copy(self._idx), Cond(idx=Ignore, idx, Length(arg)>1, ApplyFunc(idx.set_rng, self.simt_range(arg[2])), ApplyFunc(idx.set_rng, self.simt_range(1)) ) ),
    need_cond := (self, i) >> let(L := Length(self.params), i < L and L > 1 and (self.params[i+1] <> [0,self.params[1]-1]) ),
    simt_cond   := (self, i) >> let( rng := self.simt_range(i), When(
                            self.need_cond(i), Cond(
                                rng[1] = 0, leq(self._idx, V(Last(rng))),
                                Last(rng) = self.params[1]-1, geq(self._idx, V(rng[1])),
                                rng[1] = Last(rng), eq(self._idx, V(rng[1])),
                                logic_and(geq(self._idx, V(rng[1])), leq(self._idx, V(Last(rng)))) 
                                ),
                            V(true)
                            )),
    update_simt_range := meth(self, i, new_rng)
        local pre, post, dim;

        dim := self;
        if ObjId(new_rng) = ObjId(dim) then
            if Length(dim.params) < i then
            dim.params := dim.params :: List([Length(dim.params)..i], p -> dim.simt_range(p)); 
            fi;
            pre  := Take(dim.params, i);
            post := When(Length(dim.params)>i+1, Drop(dim.params, i+1), []);
            dim.params := pre::new_rng.simt_all_ranges()::post;
        elif Length(dim.params) <= 2 and i = 1 then
            dim := new_rng;
        else
            if Length(dim.params) < i then
            dim.params := dim.params :: List([Length(dim.params)..i], p -> dim.simt_range(p)); 
            fi;
            pre  := [ApplyFunc( ObjId(dim), Take(dim.params, i) ) ];
            post := When(Length(dim.params)>i+1, [ApplyFunc( ObjId(dim), Drop(dim.params, i+1) )], []);
            dim := ApplyFunc(ASIMTListDim, pre::[new_rng]::post);
        fi;
        return dim;
    end, 
    simt_range  := (self, i) >> When(Length(self.params) > i, self.params[i+1], [0, self.params[1]-1]),
    simt_all_ranges := (self) >> When(Length(self.params) > 1, Drop(self.params,1), [ [0, self.params[1]-1] ]),
    simt_sync   := (self) >> skip(),
    num_ranges := (self) >> Maximum(1, Length(self.params)-1)
    ));

Class(ASIMTGridDim,  ASIMTDim, rec(
    simt_sync := (self) >> simt_syncgrid()
    ));

Class(ASIMTGridDimX,  ASIMTGridDim, rec(
    updateParams := meth(self) 
        self._idx := self._build_gen_idx(simtBlockIdxX, self.params{[1]});
        return self;
    end,
    ));
Class(ASIMTGridDimY,  ASIMTGridDim, rec(
    updateParams := meth(self) 
        self._idx := self._build_gen_idx(simtBlockIdxY, self.params{[1]});
        return self;
    end,
    ));
Class(ASIMTGridDimZ,  ASIMTGridDim, rec(
    updateParams := meth(self) 
        self._idx := self._build_gen_idx(simtBlockIdxZ, self.params{[1]});
        return self;
    end,
    ));

Class(ASIMTBlockDim, ASIMTDim, rec(
    simt_sync := (self) >> simt_syncblock()
    ));

Class(ASIMTBlockDimX,  ASIMTBlockDim, rec(
    simt_sync := (self) >> simt_synccluster(),
    updateParams := meth(self) 
        self._idx := self._build_gen_idx(simtThreadIdxX, self.params{[1]});
        return self;
    end,
    ));
Class(ASIMTBlockDimY,  ASIMTBlockDim, rec(
    updateParams := meth(self) 
        self._idx := self._build_gen_idx(simtThreadIdxY, self.params{[1]});
        return self;
    end,
    ));
Class(ASIMTBlockDimZ,  ASIMTBlockDim, rec(
    updateParams := meth(self) 
        self._idx := self._build_gen_idx(simtThreadIdxZ, self.params{[1]});
        return self;
    end,
    ));

Class(ASIMTListDim, ASIMTDim, rec(

    _point_to_rng := meth(self, i)
        local p, curr, curr_nr;

        curr := self.params[1];
        curr_nr := curr.num_ranges();
        p := 2;
        while i > curr_nr and p <= Length(self.params) do
            i := i - curr_nr;
            curr := self.params[p];
            curr_nr := curr.num_ranges();
            p := p + 1;
        od;
        #[<inner-dim containing requested rng>, <pos of rng within inner-dim>, <pos of inner-dim in params>]
        return [curr, i, p-1];
    end,
    simt_idx    := (arg) >> let(self := arg[1], nump := Length(self.params), 
                                When(Length(arg)>1, let( d_i := self._point_to_rng(arg[2]), d_i[1].simt_idx(d_i[2]) ), 
                                                    List(self.params, p -> p.simt_idx())
                                ) ),
    need_cond := (self, i) >> let( d_i := self._point_to_rng(i), d_i[1].need_cond(d_i[2]) ),
    simt_cond   := (self, i) >> let( d_i := self._point_to_rng(i), d_i[1].simt_cond(d_i[2]) ),
    update_simt_range := meth(self, i, new_rng)
        local d_i;

        d_i := self._point_to_rng(i);
        self.params[d_i[3]] := d_i[1].update_simt_range(d_i[2], new_rng);
        
        return self;
    end, 
    num_ranges := (self) >> Sum(List(self.params, i -> i.num_ranges())),
    simt_range  := (self, i) >> let( d_i := self._point_to_rng(i), d_i[1].simt_range(d_i[2]) ),
    simt_all_ranges := (self) >> let( numi := self.num_ranges(), List([1..numi], i -> self.simt_range(i)) ),
    simt_sync   := (self) >> Maximum( List(self.params, p -> p.simt_sync()) ),
    simt_dim    := (self, i) >> self.params[i],
    simt_dim_at := (self, i) >> let( d_i := self._point_to_rng(i), d_i[1])
    ));

Class(ASIMTLoopDim,  ASIMTDim, rec(
    simt_range  := (self, i) >> [],
    simt_all_ranges := (self) >> [],
    num_ranges := (self) >> 0,
    update_simt_range := meth(self, i, new_rng)
        local dim;

        dim := self;
        if ObjId(new_rng) <> ObjId(dim) then
            dim := When(i=1, new_rng, ApplyFunc(ASIMTListDim, Replicate(i-1, dim)::[new_rng]) );
        fi;
        return dim;
    end,
    ));

Class(ASIMTFlag, ASIMTDim, rec(
    updateParams := meth(self)
        self._simt_dim := self.params[1];
    end,
    simt_dim    := (self) >> self._simt_dim,
    simt_idx    := (arg) >> let(self := arg[1], ApplyFunc(self._simt_dim.simt_idx, arg{[2..Length(arg)]}) ),
    need_cond := (self, i) >> self._simt_dim.need_cond(i),
    simt_cond   := (self, i) >> self._simt_dim.simt_cond(i),
    update_simt_range := meth(self, i, new_rng)
        self._simt_dim := self._simt_dim.update_simt_range(i, new_rng);
        return self;
    end, 
    simt_range  := (self, i) >> self._simt_dim.simt_range(i),
    simt_all_ranges := (self) >> self._simt_dim.simt_all_ranges(),
    simt_sync   := (self) >> self._simt_dim.simt_sync(),
    num_ranges := (self) >> self._simt_dim.num_ranges()
    ));

Class(ASIMTKernelFlag, ASIMTFlag);

Class(ASIMTFissionFlag, ASIMTFlag);

Class(ASIMTTileFlag, ASIMTFlag, rec(
    updateParams := meth(self)
        Inherited();
        self._tsize  := self.params[2];
    end,
    
    tsize := (self) >> self._tsize
    ));

IsASIMTDim := (tag) -> ObjId(tag) in ASIMTDim._all_descendants();

##### Wrapping ######

Class(PlaceHolderMat, BaseMat, rec(
    
    abbrevs := [ (id, ttype, dims) -> [ rec( 
                            id := id,
                            TType := Copy(ttype),
                            dimensions := Copy(dims) ) ] ],

    new := (self, spl) >> let( is_spl := IsSPL(spl), SPL(WithBases(self, rec( 
                            id := When(is_spl, var._id(""), spl.id),
                            TType := When(is_spl, Copy(spl.TType), spl.TType),
                            dimensions := When(is_spl, Copy(spl.dimensions), spl.dimensions) )))
                        ),

    from_rChildren := (self, rch) >> ApplyFunc(ObjId(self), rch).appendAobj(self),
    
    rChildren := (self) >> [ self.id, self.TType, self.dimensions ],
    rSetChild := rSetChildFields("id", "TType", "dimensions"), 

    rng := meth(self) local d;
        d := [self.dimensions[1]];
        if IsBound(self.a.t_out) then
            return List(TransposedMat([self.a.t_out, d]), e -> TArray(e[1], e[2]));
        else
            return List(d, e -> TArray(self.TType, e));
        fi;
    end,

    dmn := meth(self) local d;
        d := [self.dimensions[2]];
        if IsBound(self.a.t_in) then
            return List(TransposedMat([self.a.t_in, d]), e -> TArray(e[1], e[2]));
        else
            return List(d, e -> TArray(self.TType, e));
        fi;
    end,

    ));

wrap_rule_apply := function(rules, wrapper)
    local rule;
    rules := Flat([rules]);
    for rule in rules do
        if IsNewRule(rule) then
            rule._apply := rule.apply;
            rule.apply := wrapper(rule);
        else 
            rule._rule := rule.rule;
            rule.rule  := wrapper(rule);
        fi;
    od;

end;

unwrap_rule_apply := function(rules)
    local rule;
    rules := Flat([rules]);
    for rule in rules do    
        if IsNewRule(rule) then
            rule.apply := rule._apply;
        else rule.rule := rule._rule;
        fi;
    od;

end;

_original_apply := (R, nt, children, nonterms) -> Checked(IsRule(R), IsSPL(nt),
    When(IsNewRule(R), 
     R._apply(nt, children, nonterms),
     When(NumGenArgs(R._rule)=2, 
          R._rule(nt.params, children),
          R._rule(nt.params, children, nonterms)))
);

dummy_wrap := (R) -> ( (nt, c, cnt) -> let(PrintLine("Using wrapped rule."), _apply(R, nt, c, cnt)) );

_strl := (n, c) -> StringJoin("", Replicate(n, c));


TaggableOps := [Tensor, SUM, ISum, DirectSum, IDirSum, VStack, IterVStack, HStack1, IterHStack1];

wrap_apply := (R) -> function(arg)
                        local nt, c, cnt, simt_exp, simt_dims, phs, ss;        

                        nt := arg[1]; c := arg[2]; cnt := arg[3];

                        # Use placeholders for children to prevent Collect from going beyond rule.apply's boundaries
                        phs := List(c, spl -> PlaceHolderMat(spl));
                        simt_exp := _original_apply(R, nt, phs, cnt);  # This dispatches to right call: _rule (for Rules) or _apply (for NewRules)
                        ss := Collect(simt_exp, @(1, TaggableOps) );

                        simt_dims := let( cd := nt.getA("simt_dim", [ASIMTLoopDim()]), 
                                        Cond(cd=Ignore, [], 
                                             IsList(cd) and Length(cd) = 1, Replicate(Length(ss), cd[1]), 
                                             cd)
                                    );
                        if Length(simt_dims) <> Length(ss) then
                            Error("Number of tags (", Length(simt_dims), ") <> number of taggable operators (", Length(ss), ")");
                        fi;

                        # PrintLine("@@@@@@@@@@@@@ Beg ", R, "@@@@@@@@@@@@@@@");
                        # PrintLine("NT      >> ", nt);
                        # PrintLine("simt_dims >> ", simt_dims);
                        # PrintLine("simt_expr >>", simt_exp);
                        # PrintLine("phs     >>", phs);
                        # PrintLine("ch      >>", c);
                        # PrintLine("@@@@@@@@@@@@@ End ", R, "@@@@@@@@@@@@@@@");

                        for i in [1..Length(ss)] do
                            simt_exp := SubstTopDownNR(simt_exp, @(1, ObjId(ss[i])).cond(e->e=ss[i]), 
                                        e -> ApplyFunc(AllClasses.("SIMT"::ObjId(ss[i]).name), [simt_dims[i], ss[i]]));
                        od;

                        for i in [1..Length(c)] do
                            simt_exp := SubstTopDownNR(simt_exp, @(1).cond(e->e=phs[i]), e -> c[i] );
                        od;

                        return simt_exp;
                    end;

# Node of a TagTree
tag_rec := (tag, tag_list) -> rec(simt_dim := tag, ch_tags := tag_list);

# Merge RuleTree and TagTree
tmp_tag_rt := function(rt, dims, opts)
    if dims = Ignore then
        rt.node := rt.node.setA(["simt_dim", [ASIMTLoopDim()] ]);
        DoForAll([1..Length(rt.children)], i -> tmp_tag_rt(rt.children[i], dims, opts) );
    elif IsASIMTDim(dims) then
        rt.node := rt.node.setA(["simt_dim", [dims] ]);
        DoForAll([1..Length(rt.children)], i -> tmp_tag_rt(rt.children[i], Ignore, opts) );
    elif IsList(dims) then
        rt.node := rt.node.setA(["simt_dim", [ASIMTLoopDim()] ]);
        DoForAll([1..Length(rt.children)], i -> tmp_tag_rt(rt.children[i], dims[i], opts) );
    else
        rt.node := rt.node.setA(["simt_dim", dims.simt_dim]);
        DoForAll([1..Length(rt.children)], i -> tmp_tag_rt(rt.children[i], dims.ch_tags[i], opts) );
    fi;
end;
