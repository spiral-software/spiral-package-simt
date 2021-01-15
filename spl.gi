# A Taggable operator (see tags.gi) is translated into an analogous SIMT operator that carries dim tag info
 
Class(SIMTTensor, Tensor, rec(

    abbrevs := [ (simt_dim, spl) -> When(IsASIMTDim(simt_dim) and ObjId(spl) = Tensor, [Flat([simt_dim, spl._children])], [[simt_dim, spl]] )  ]
                :: Tensor.abbrevs,

    new := meth(self, arg)
        local simt_dim, L;
        Constraint(IsList(arg) and Length(arg) >= 2);
        simt_dim := arg[1];
        L := arg{[2..Length(arg)]};
        L:=Filtered(L,x->x<>I(1));
        if (Length(L)=0) then return I(1); fi;
        if Length(L)=1 then return L[1]; fi;

        return SPL(WithBases( self, 
                        rec( simt_dim := simt_dim,
                             _children := L,
                             dimensions := [ Product(L, t -> t.dims()[1]),
                                             Product(L, t -> t.dims()[2]) ] )));
    end,

    from_rChildren := (self, rch) >> ApplyFunc(ObjId(self), [self.simt_dim]::rch).appendAobj(self)
    
    ));

Class(SIMTISum, ISum, rec(

    abbrevs := [ (simt_dim, spl) -> When(IsASIMTDim(simt_dim) and ObjId(spl) = ISum, [simt_dim, spl.var, spl.domain, spl._children[1]], [simt_dim, spl] )  ],

    new := meth(self, simt_dim, var, domain, expr)
        local res;
        Constraint(IsSPL(expr));
        # if domain is an integer (not symbolic) it must be positive
        Constraint(not IsInt(domain) or domain >= 0);
        var.isLoopIndex := true;
        res := SPL(WithBases(self, rec(_children := [expr], simt_dim := simt_dim, var := var, domain := domain)));
        res.dimensions := res.dims();
        return res;
    end,

    print := (self, i, is) >> Print(
        self.name, "(", self.simt_dim, ", ", self.var, ", ", self.domain, ",\n",
        Blanks(i+is), self._children[1].print(i+is, is), "\n",
        Blanks(i), ")", self.printA(),
        When(IsBound(self._setDims), Print(".overrideDims(", self._setDims, ")"), Print(""))
    )

    ));

Class(SIMTSUM, SUM, rec(

    new := meth(self, arg)
        local dims, simt_dim, L;
        Constraint(IsList(arg) and Length(arg) >= 2);
        simt_dim := arg[1];
        L := arg{[2..Length(arg)]};
        Constraint(Length(L) >= 1); Constraint(ForAll(L, IsSPL));
#        if Length(L) = 1 then return L[1]; fi;
        dims := L[1].dims();
        if not (IsSymbolic(dims[1]) or IsSymbolic(dims[2])) and
           not ForAll(Drop(L, 1), x -> let(d:=x.dims(),
                   IsSymbolic(d[1]) or IsSymbolic(d[2]) or d = dims))
            then Error("Dimensions of summands do not match"); fi;
        return SPL(WithBases(self, rec( simt_dim := simt_dim, _children := L, dimensions := dims)));
    end,

    from_rChildren := (self, rch) >> ApplyFunc(ObjId(self), [self.simt_dim]::rch).appendAobj(self),

    print := meth(self, i, is) 
        local s, first, newline;

        if self._short_print or ForAll(self._children, x->not IsRec(x) or IsSPLSym(x) or IsSPLMat(x)) then
            newline := Ignore;
        else 
            newline := self._newline;
        fi;
        first := true;
        Print(self.name, "( ", self.simt_dim, ",");
        for s in self._children do
                if(first) then first:=false;
                else Print(", "); fi;
                newline(i + is);
                When(IsSPL(s) or (IsRec(s) and IsBound(s.print) and NumGenArgs(s.print)=2),
                    s.print(i + is, is), 
                    Print(s));
        od;
        newline(i);
        Print(")");
        self.printA();

        if IsBound(self._setDims) then
            Print(".overrideDims(", self._setDims, ")");
        fi;
    end,
    
    ));

Class(SIMTDirectSum, DirectSum, rec(

    abbrevs := [ arg ->
        [ Filtered(
            Flat(List(Flat(arg),
                s -> When(IsSPL(s) and ObjId(s)=DirectSum, s.children(), s))), x-> IsASIMTDim(x) or x.dimensions<>[0,0]) ]
    ],

    new := meth(self, arg)
        local simt_dim, L;
        Constraint(IsList(arg) and Length(arg) >= 2);
        simt_dim := arg[1];
        L := arg{[2..Length(arg)]};
        if ForAll(L, IsIdentitySPL)
            then return I(Sum(L, Rows));
        else
            return SPL(WithBases( self,
            rec( simt_dim := simt_dim, _children := L,
            dimensions := [ Sum(L, t -> t.dimensions[1]),
                            Sum(L, t -> t.dimensions[2]) ] )));
        fi;
    end,

    from_rChildren := (self, rch) >> ApplyFunc(ObjId(self), [self.simt_dim]::rch).appendAobj(self)
    
    ));

Class(SIMTVStack, VStack, rec(

    abbrevs := [ (simt_dim, spl) -> When(IsASIMTDim(simt_dim) and ObjId(spl) = VStack, [Flat([simt_dim, spl._children])], [[simt_dim, spl]] )  ]
                :: VStack.abbrevs,

    new := (self, arg) >> let(simt_dim := Checked(IsList(arg), arg[1]), spls := arg{[2..Length(arg)]}, 
                                Checked(
                                    Length(spls) >= 1, 
                                    ForAll(spls, s -> IsSymbolic(Cols(s)) or IsSymbolic(Cols(spls[1])) or Cols(s) <= Cols(spls[1])),
                                    SPL(WithBases(self, rec(simt_dim := simt_dim, _children := spls)).setDims())
                                )
                            ),

    from_rChildren := (self, rch) >> ApplyFunc(ObjId(self), [self.simt_dim]::rch).appendAobj(self)

    ));

Class(SIMTHStack, HStack, rec(

    abbrevs := [ (simt_dim, spl) -> When(IsASIMTDim(simt_dim) and ObjId(spl) = HStack, [Flat([simt_dim, spl._children])], [[simt_dim, spl]] )  ]
                :: HStack.abbrevs,

    new := (self, arg) >> let(simt_dim := Checked(IsList(arg), arg[1]), spls := arg{[2..Length(arg)]}, 
                                Checked(
                                    IsList(spls), 
                                    Length(spls) >= 1, 
                                    ForAll(spls, s->Rows(s)<=Rows(spls[1])),
                                    SPL(WithBases(self, rec(simt_dim := simt_dim, _children := spls)).setDims())
                                )
                            ),

    from_rChildren := (self, rch) >> ApplyFunc(ObjId(self), [self.simt_dim]::rch).appendAobj(self)

));

Class(SIMTHStack1, SIMTHStack);

Class(SIMTBaseIterative, BaseIterative, rec(

    abbrevs := [ (simt_dim, spl) -> When(IsASIMTDim(simt_dim) and IsIterative(spl), [simt_dim, spl.var, spl.domain, spl._children[1]], [simt_dim, spl] )  ],

    new := meth(self, simt_dim, var, domain, expr)
        local res;
        Constraint(IsSPL(expr));
        # if domain is an integer (not symbolic) it must be positive
        Constraint(not IsInt(domain) or domain >= 0);
        var.isLoopIndex := true;
        res := SPL(WithBases(self, rec(_children := [expr], simt_dim := simt_dim, var := var, domain := domain)));
        res.dimensions := res.dims();
        return res;
    end,

    print := (self, i, is) >> Print(
        self.name, "(", self.simt_dim, ", ",  self.var, ", ", self.domain, ",\n",
        Blanks(i+is), self._children[1].print(i+is, is), "\n",
        Blanks(i), ")", self.printA(),
        When(IsBound(self._setDims), Print(".overrideDims(", self._setDims, ")"), Print(""))
    )
));

Class(SIMTIterVStack, SIMTBaseIterative, rec(
    dims := self >> [ self.child(1).dimensions[1] * self.domain,
                      self.child(1).dimensions[2] ],
));

Class(SIMTIterHStack, SIMTBaseIterative, rec(
    dims := self >> [ self.child(1).dimensions[1],
                      self.child(1).dimensions[2] * self.domain ],
));

Class(SIMTIterHStack1, SIMTIterHStack);

Class(SIMTIDirSum, SIMTBaseIterative, rec(
    dims := self >> let(d:=self._children[1].dimensions, [d[1]* self.domain, d[2]*self.domain])
));

Class(SIMTGrp, Grp);
