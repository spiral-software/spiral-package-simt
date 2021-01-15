# SIMT-operators transfer their dim tag info to SIMT-SUM/ISum operators when SPL is lowered to SigmaSPL

Class(SIMTSumsGen, DefaultSumsGen, rec(

    _directSumSIMTSums := (self, obj, roverlap, coverlap, opts) >>
        let(cspans  :=  BaseOverlap.spans(roverlap, List(obj.children(), Cols)),
            rspans  :=  BaseOverlap.spans(coverlap, List(obj.children(), Rows)),
            nblocks  :=  obj.numChildren(),
            C  :=  Cols(obj),
            R  :=  Rows(obj),
            OP  :=  When(coverlap > 0, SUMAcc, SIMTSUM),
            OP( When(OP=SIMTSUM, [obj.simt_dim], []) :: Map([1..nblocks],
                 i -> Compose( 
                      WID(R, 1 + rspans[i][2] - rspans[i][1], rspans[i][1]-1),
                      self(obj.child(i), opts),
                      RID(C, 1 + cspans[i][2] - cspans[i][1], cspans[i][1]-1) )))
            ),

    SIMTDirectSum := (self, o, opts) >> Cond(o.isPermutation(),
    Prm(ApplyFunc(fDirsum, List(o.children(), c->self(c, opts).func))),
        self._directSumSIMTSums(o, 0, 0, opts)
    ),

    IDirSum := (self, o, opts) >> let(
        bkcols := Cols(o.child(1)),
        bkrows := Rows(o.child(1)),
        nblocks := o.domain,
        cols := Cols(o), 
        rows := Rows(o),

        SIMTISum(o.simt_dim, o.var, o.domain,
            Compose(Scat(fTensor(fBase(nblocks, o.var), fId(bkrows))),
                self(o.child(1), opts),
                Gath(fTensor(fBase(nblocks, o.var), fId(bkcols)))))
    ),

    SIMTTensor := meth(self, o, opts)
        local ch, col_prods, row_prods, col_prods_rev, row_prods_rev, i, j1, j2, j1b, j2b, bkcols, bkrows, prod, term;

        if o.isPermutation() then 
            return Prm(ApplyFunc(o.fTensor, List(o.children(), c->self(c, opts).func)));
        elif ForAll(o.children(), x->ObjId(x)=Diag) then 
            return Diag(ApplyFunc(diagTensor, List(o.children(), c->c.element)));
        fi;

        ch := o.children();
        col_prods := ScanL(ch, (x,y)->x*Cols(y), 1);
        col_prods_rev := Drop(ScanR(ch, (x,y)->x*Cols(y), 1), 1);

        row_prods := ScanL(ch, (x,y)->x*Rows(y), 1);
        row_prods_rev := Drop(ScanR(ch, (x,y)->x*Rows(y), 1), 1);

        prod := [];
        for i in [1..Length(ch)] do
            if not IsIdentitySPL(ch[i]) then
                bkcols := Cols(ch[i]);
                bkrows := Rows(ch[i]);
                j1 := Ind(col_prods[i]);
                j2 := Ind(row_prods_rev[i]);
                j1b := When(j1.range = 1, 0, fBase(j1));
                j2b := When(j2.range = 1, 0, fBase(j2));
            
                term := Scat(o.scatTensor(i)(Filtered([j1b, fId(bkrows), j2b], x->x<>0))) *
                        self(ch[i], opts) *
                    Gath(o.gathTensor(i)(Filtered([j1b, fId(bkcols), j2b], x->x<>0)));
            
                if j2.range <> 1 then
                    term := SIMTISum(o.simt_dim, j2, j2.range, term); 
                fi;
            
                if j1.range <> 1 then
                    term := SIMTISum(o.simt_dim, j1, j1.range, term); 
                fi;
            
                Add(prod, term);
            fi;
        od;
        return Compose(prod);
    end,

    SIMTISum := (self, o, opts) >> CopyFields(o, rec(_children := [self(o._children[1], opts)])),

    SIMTIDirSum := (self, o, opts) >> let(
        bkcols := Cols(o.child(1)),
        bkrows := Rows(o.child(1)),
        nblocks := o.domain,
        cols := Cols(o), 
        rows := Rows(o),

        SIMTISum(o.simt_dim, o.var, o.domain,
            Compose(Scat(fTensor(fBase(nblocks, o.var), fId(bkrows))),
                self(o.child(1), opts),
                Gath(fTensor(fBase(nblocks, o.var), fId(bkcols)))))
    ),

    SIMTVStack := (self, o, opts) >> let(       
        ch   := List(o.children(), e -> self(e, opts)),
        l    := Length(ch),
        ofs  := ScanL(ch, (p,x)->p+Rows(x), 0),
        SIMTSUM(o.simt_dim, List([1..l], i -> 
            Scat(H(Rows(o), Rows(ch[i]), ofs[i], 1)) * ch[i] * Gath(fId(Cols(o)))))
    ),

    SIMTHStack1 := (self, o, opts) >> let(      
        ch   := List(o.children(), e -> self(e, opts)),
        l    := Length(ch),
        it0  := Scat(fId(Rows(o))) * ch[1] * Gath(H(Cols(o), Cols(ch[1]), 0, 1)), 
        ofs  := ScanL(ch, (p,x)->p+Cols(x), 0),
        its  := List([2..l], i -> 
                   Scat(fId(Rows(o))) * ch[i] * Gath(H(Cols(o), Cols(ch[i]), ofs[i], 1))), 
        SIMTSUM(o.simt_dim, [it0] :: its )
    ),

    SIMTIterVStack := (self, o, opts) >> let(
        bkcols := Cols(o.child(1)),
        bkrows := Rows(o.child(1)),
        nblocks := o.domain,
        cols := Cols(o), rows := Rows(o),
        SIMTISum(o.simt_dim, o.var, o.domain,
            Scat(fTensor(fBase(nblocks, o.var), fId(bkrows))) *
            self(o.child(1), opts) *
            Gath(fId(bkcols)))
    ),

    SIMTIterHStack1 := (self, o, opts) >> let(
        bkcols := Cols(o.child(1)),
        bkrows := Rows(o.child(1)),
        nblocks := o.domain,
        cols := Cols(o), rows := Rows(o),
        j := Ind(nblocks),
        ch := self(o.child(1), opts),

        SIMTISum(o.simt_dim, j, j.range,
        Scat(fId(bkrows)) *
        SubstVars(Copy(ch), rec((o.var.id) := j)) *
        Gath(fTensor(fBase(nblocks, j), fId(bkcols)))
        )
    ),

    ));
