
##  Copyright (c) 2018-2021, Carnegie Mellon University
##  See LICENSE for details

# Icode objects that are not cuda-specific (those are defined in cuda_icode.gi)

# A simt index is derived from a SIMT dim tag

Class(simtIdx, Exp, rec(
    computeType := (self) >> TInt,
    
    size := self >> When(Length(self.args)>0, self.args[1], 0),

    count := (self) >> let(rng := self.get_rng(), When(rng<>[], rng[2]-rng[1]+1, 0 ) ),

    set_rng := meth(self, l, h)
        if Length(self.args)>1 then
            self.args[2] := [l, h];
        else
            Add(self.args, [l, h]);
        fi;
        return self;
    end,
    
    eval := self >> self,
    
    can_fold := False,

    get_rng := (self) >> Cond(Length(self.args)>1, When(IsValue(self.args[2]), self.args[2].v, self.args[2]), Length(self.args)>0, [0, self.args[1]-1], [])

));

Class(simtBlockIdx, simtIdx);
Class(simtThreadIdx, simtIdx);

Class(simtBlockIdxX, simtBlockIdx);
Class(simtBlockIdxY, simtBlockIdx);
Class(simtBlockIdxZ, simtBlockIdx);

IsSimtBlockIdx := (idx) -> ObjId(idx) in simtBlockIdx._all_descendants();

Class(simtThreadIdxX, simtThreadIdx);
Class(simtThreadIdxY, simtThreadIdx);
Class(simtThreadIdxZ, simtThreadIdx);

IsSimtThreadIdx := (idx) -> ObjId(idx) in simtThreadIdx._all_descendants();

# Used to identify blocks of code that can be mapped to a kernel
Class(simt_block, chain);

Class(simt_loop, loop, rec(
    drop_range1 := false,

    __call__ := meth(self, simt_idx, loopvar, range, cmd)
        local result;
        Constraint(IsCommand(cmd));
        if IsSymbolic(range) then return loopn(loopvar, range, cmd); fi;
        range := toRange(range);
        if self.drop_range1 and range = 1 then
            return SubstBottomUp(Copy(cmd), @(1, var, e->e=loopvar), e->V(0));
        elif range = 0 then
            return skip();
        elif simt_idx = Ignore then
            return loop(loopvar, range, cmd);
        else
            loopvar.setRange(range);
            range := listRange(range);
            result := WithBases(self,
                rec(operations := CmdOps, simt_idx := simt_idx, cmd := cmd, var := loopvar, range := range));
            loopvar.isLoopIndex := true;
            #loopvar.loop := result;
            return result;
        fi;
    end,

    rChildren := self >> [self.simt_idx, self.var, self.range, self.cmd],
    rSetChild := rSetChildFields("simt_idx", "var", "range", "cmd"),

    ));

# A function that allows declaration specifiers (eg, __global__, __device__, etc..)
Class(specifiers_func, func, rec(
    __call__ := (self, decl_specs, ret, id, params, cmd) >> WithBases(self, rec(
            decl_specs := Checked(IsList(decl_specs), decl_specs),
            ret    := Checked(IsType(ret), ret),
            id     := Checked(IsString(id), id),
            params := Checked(IsList(params), params),
            cmd    := Checked(IsCommand(cmd), cmd),
            operations := CmdOps)),

    rChildren := self >> [self.decl_specs, self.ret, self.id, self.params, self.cmd],
    rSetChild := rSetChildFields("decl_specs", "ret", "id", "params", "cmd"),

    print := (self, i, si) >> Print(self.__name__, "(", self.decl_specs, ", ", self.ret, ", \"", self.id, "\", ", self.params, ", \n",
        Blanks(i+si), self.cmd.print(i+si, si), "\n", Blanks(i), ")", self.printA()),
    )
);

# sync primitives. Their relationship is defined by their sync scope (cluster < block < grid).
# A grid is composed of blocks and blocks of clusters (eg, cuda: grid, blocks, warps).

Class(simtSyncOps, CmdOps, rec(
    \< := (v1, v2) -> Cond(
                            ObjId(v1) = ObjId(v2) or ObjId(v1) = simt_syncgrid, false,
                            ObjId(v1) = skip, true,
                            ObjId(v1) = simt_synccluster and ObjId(v2) <> skip, true,
                            ObjId(v1) = simt_syncblock and not ObjId(v2) in [skip, simt_synccluster], true,
                            false
                        )
    ));

Class(simt_sync, call, rec(
    __call__ := (arg) >> let(o := Inherited(), CopyFields(o, rec(operations := simtSyncOps) ) ) 
    ));

Class(simt_synccluster, simt_sync);

Class(simt_syncblock, simt_sync);

Class(simt_syncgrid, simt_sync);

# unparsed into C-style printf

Class(cprintf, call);
