
##  Copyright (c) 2018-2021, Carnegie Mellon University
##  See LICENSE for details

Class(CudaUnparser, CUnparser, rec(

    simt_loop := meth(self, o, i, is) 
        local v, lo, hi, l_cond, r_cond, simt_idx, simt_rng, body;
        
        v := o.var; lo := o.range[1]; hi := Last(o.range); 
        simt_idx := o.simt_idx;
        simt_rng := o.simt_idx.get_rng();
        body := Copy(o.cmd);
        l_cond := simt_rng[1]>0; r_cond := simt_rng[2] < simt_idx.size()-1;

        if (hi-lo) < simt_rng[2]-simt_rng[1] then
            body := SubstVars(body, rec((v.id) := simt_idx + lo - simt_rng[1]));
            Print(Blanks(i), "if( ");
            if l_cond then
                Print(self(simt_idx, 0, 0), " >= ", self(simt_rng[1], 0, 0), " && ");
            fi;
            Print(self(simt_idx, 0, 0), " <= ", self(simt_rng[1]+hi-lo, 0, 0), " ) {\n",
                self(body, i+is, is),
                Blanks(i), "}\n");            
        elif (hi-lo) = simt_rng[2]-simt_rng[1] then
            body := SubstVars(body, rec((v.id) := simt_idx + lo - simt_rng[1]));
            if l_cond or r_cond then
                Print(Blanks(i), "if( ");
                if l_cond then
                    Print(self(simt_idx, 0, 0), " >= ", self(simt_rng[1], 0, 0));
                fi;
                if l_cond and r_cond then
                    Print(" && ");
                fi;
                if r_cond then
                    Print(self(simt_idx, 0, 0), " <= ", self(simt_rng[2], 0, 0));
                fi;
                Print(" ) {\n");
            fi;
            self(body, When(l_cond or r_cond, i+is, i), is);
            if l_cond or r_cond then
                Print(Blanks(i), "}\n");
            fi;
        else
            body := SubstVars(body, rec((v.id) := simt_idx + v - simt_rng[1]));
            Print(When(IsBound(self.opts.looppragma), self.opts.looppragma(o,i,is)),
                Blanks(i), "for(int ", v, " = ", lo, "; ");
            if l_cond then
                Print(self(simt_idx + v-simt_rng[1], 0, 0), " >= ", lo, " && ");
            fi;
            Print(self(simt_idx + v-simt_rng[1], 0, 0), " <= ", hi, "; ", 
                v, "+=", self(simt_rng[2]-simt_rng[1]+1, 0, 0), ") {\n",
                self(body, i+is, is),
                Blanks(i), "}\n");
        fi;

    end,

    Dim3 := meth(self,t,vars,i,is)
        local v, var_list;
        Print("dim3 ");
        var_list := List(vars, v-> v.id::"("::StringJoin(", ", List([v.x.value, v.y.value, v.z.value], v -> When(IsValue(v), v.v, v) ) )::")");
        self.infix(var_list, ", ");
    end,

    TArray := meth(self,t,vars,i,is)
        local dims, elt, v, ptype, vsize, var_specs;
        if Length(vars) > 1 then DoForAll(vars, v->Print(self.TArray(t, [v], i, is), "; "));
        elif Length(vars) = 0 then
            Print(self.declare(t.t, [], i, is), " *");
        else
            # at this point Length(vars)=1
            v := When(IsList(vars), vars[1], vars);
            var_specs := When(IsBound(v.decl_specs), v.decl_specs, []);
            dims := []; elt := t;
            while IsArray(elt) do Add(dims, elt.size); elt := elt.t; od;

            #FIXME/HACK: Ignoring twiddles by looking for "D" in .id
            # Better way: look for func.name="init" in parent/context
            if IsBound(self.opts.useMemoryArena) and self.opts.useMemoryArena and v.id[1] <> 'D' then
                #FIXME: Arena currently doesn't handle multiple dims.
                #FIXME: Slightly ugly hack to get this to be a pointer

                # To handle vectors. Arena is declared only for scalars. For
                # vectors, we must manually scale the allocation by vector length.
                vsize := 1; if ObjId(elt)=TVect then vsize := elt.size; fi;
                ptype := Concatenation(elt.name, "Pointer");
                self.(ptype)(elt, [v], i, is);
                Print(" =  &(ARENA[ (arenalevel-=",self(dims[1]*vsize,i,is),") ])");
            else
                if var_specs <> [] then
                    Print(self.infix(var_specs, " "), " ");
                fi;
                if IsBound(v.decl_as_ptr) and v.decl_as_ptr then
                    Print(self.declare(t.t, [], i, is), "*", v.id);
                else
                    self.(elt.name)(elt, [v], i, is);
                    DoForAll(dims, d->Print("[",self(d,i,is),"]"));
                fi;
            fi;

        fi;
    end,

    T_CudaEvent := (self, t, vars, i, is) >> 
        Print("cudaEvent_t ", self.infix(vars, ", ", i + is)),

    cu_event_create := (self, o, i, is) >> Print(Blanks(i), "cudaEventCreate(", self(o.args[1], 0, 0), 
                            When(Length(o.args)>1 and not o.args[2].v, ")", ");\n")),

    cu_event_record := (self, o, i, is) >> Print(Blanks(i), "cudaEventRecord(", self(o.args[1], 0, 0), 
                            When(Length(o.args)>1 and not o.args[2].v, ")", ");\n")),

    cu_event_destroy := (self, o, i, is) >> Print(Blanks(i), "cudaEventDestroy(", self(o.args[1], 0, 0), 
                            When(Length(o.args)>1 and not o.args[2].v, ")", ");\n")),

    cu_event_elapsed_time := (self, o, i, is) >> Print(Blanks(i), "cudaEventElapsedTime", 
                                self.pinfix(o.args{[1..3]}, ", "), 
                                When(Length(o.args)>3 and not o.args[4].v, "", ";\n")),
    
    cu_event_synchronize := (self, o, i, is) >> Print(Blanks(i), "cudaEventSynchronize(", self(o.args[1], 0, 0), 
                            When(Length(o.args)>1 and not o.args[2].v, ")", ");\n")),

    cu_device_synchronize := (self, o, i, is) >> Print(Blanks(i), "cudaDeviceSynchronize(",
                            When(Length(o.args)>0 and not o.args[1].v, ")", ");\n")),

    cprintf := (self, o, i, is) >> Print(Blanks(i), "printf(\"", o.args[1].v, "\", ", 
                                            self.infix(o.args{[2..Length(o.args)]}, ", "), ");\n"),

    func := (self, o, i, is) >> let(
        parameters:=Flat(o.params),
        id := Cond(o.id="transform" and IsBound(self.opts.subName),
                     self.opts.subName,
                   o.id="init"      and IsBound(self.opts.subName),
                     Concat("init_",self.opts.subName),
                   o.id="destroy"      and IsBound(self.opts.subName),
                     Concat("destroy_",self.opts.subName),
                   o.id),
		When ((IsBound(self.opts.wrapCFuncs) and self.opts.wrapCFuncs), Print("\nextern \"C\" {")),
        Print("\n", Blanks(i),
            self.opts.funcModifier, self.declare(o.ret, var(id, o.ret), i, is), "(",
            DoForAllButLast(parameters, p->Print(self.declare(p.t, p,i,is), ", ")),
            When(Length(parameters)>0, self.declare(Last(parameters).t, Last(parameters),i,is), ""), ") ",
            "{\n",
            When(IsBound(self.opts.postalign), DoForAll(parameters, p->self.opts.postalign(p,i+is,is))),
            self(o.cmd, i+is, is),
            Blanks(i),
            "}\n"),
		When ((IsBound(self.opts.wrapCFuncs) and self.opts.wrapCFuncs), Print("}\n"))),

    specifiers_func := (self, o, i, is) >> let(
        parameters:=Flat(o.params),
        id := o.id,
        Print("\n", Blanks(i),
            self.opts.funcModifier, self.infix(o.decl_specs, " "), " ", self.declare(o.ret, var(id, o.ret), i, is), "(",
            DoForAllButLast(parameters, p->Print(self.declare(p.t, p,i,is), ", ")),
            When(Length(parameters)>0, self.declare(Last(parameters).t, Last(parameters),i,is), ""), ") ",
            "{\n",
            When(IsBound(self.opts.postalign), DoForAll(parameters, p->self.opts.postalign(p,i+is,is))),
            self(o.cmd, i+is, is),
            Blanks(i),
            "}\n")),

    cu_call := (self, o, i, is) >>
        Print(Blanks(i), o.func, 
                "<<<",
                self.infix([o.dim_grid, o.dim_block], ", "),
                ">>>",
                self.pinfix(o.args, ", "), ";\n"),

    cu_allocate := (self, o, i, is) >> Print(Blanks(i),
        "cudaMalloc(&",
        self(o.loc, 0, 0), ", ", self(o.size, 0, 0), "*sizeof(", self.declare(o.type,[], 0, 0), "));\n"),

    cu_allocate_managed := (self, o, i, is) >> Print(Blanks(i),
        "cudaMallocManaged(&",
        self(o.loc, 0, 0), ", ", self(o.exp.size, 0, 0), "*sizeof(", self.declare(o.exp.t,[], 0, 0), "));\n"),

    cu_memcpy := (self, o, i, is) >> Print(Blanks(i),
        "cudaMemcpy(", self(o.loc, 0, 0), ", ", self(o.exp, 0, 0), ", ", self(o.size, 0, 0), "*sizeof(", self.declare(o.loc.t.t,[], 0, 0), 
            "), ", o.kind, ");\n"),

    cu_memcpy_to_sym := (self, o, i, is) >> Print(Blanks(i),
        "cudaMemcpyToSymbol(", self(o.loc, 0, 0), ", ", self(o.exp, 0, 0), ", ", self(o.size, 0, 0), "*sizeof(", self.declare(o.loc.t.t,[],0,0), ") );\n"),

    cu_check_errors := (self, o, i, is) >> Print(Blanks(i), "checkCudaErrors( ", self(o.args[1], 0, 0), " );\n"), 

    cu_free := (self, o, i, is) >> Print(Blanks(i), "cudaFree(", self(o.args[1], 0, 0), ");\n"),

#    cospi := (self,o,i,is) >> Print("_"::o.name, self.pinfix(o.args, ", ")),
#    sinpi := (self,o,i,is) >> Print("_"::o.name, self.pinfix(o.args, ", ")),

    simtThreadIdxX := (self, o, i, is) >> Print("threadIdx.x"),
    simtThreadIdxY := (self, o, i, is) >> Print("threadIdx.y"),
    simtThreadIdxZ := (self, o, i, is) >> Print("threadIdx.z"),

    simtBlockIdxX := (self, o, i, is) >> Print("blockIdx.x"),
    simtBlockIdxY := (self, o, i, is) >> Print("blockIdx.y"),
    simtBlockIdxZ := (self, o, i, is) >> Print("blockIdx.z"),

    simt_syncgrid := (self, o, i, is) >> Error("Grid-level sync not supported."),
    simt_syncblock := (self, o, i, is) >> Print(Blanks(i), "__syncthreads();\n"),
    simt_synccluster := (self, o, i, is) >> Print(Blanks(i), "__syncwarp();\n")

    ));


CudaDefaults := CopyFields(SpiralDefaults, 
                                rec(
                                    globalUnrolling := 10,
                                    useDeref := false,
                                    generateInitFunc := false,
                                    includes := [],
                                    arrayBufModifier := "",
                                    arrayDataModifier := "",

                                    mempool := true,
                                    use_shmem := true,
                                    gpu_timing := true,
                                    sumsgen := SIMTSumsGen,
                                    codegen :=  CudaCodegen,
                                    unparser := CudaUnparser,
                                    cuda_version := "10.1",
                                )
                    );

TitanVDefaults := CopyFields(CudaDefaults, 
                                rec(
                                    codename := "GV100-400-A1",
                                    max_l1_size := 128*1024,
                                    max_shmem_size := 96*1024,
                                    l2_size := 4.5*2^20,
                                    devmem_size := 12*2^30
                                )
                    );
