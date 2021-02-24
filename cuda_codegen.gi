
##  Copyright (c) 2018-2021, Carnegie Mellon University
##  See LICENSE for details

#############################################################################
##
#F  MergeAndGroupRecord(<dst>,<rec1>,<rec2>...)  . . . . . . . merge the fields of records. Same fields get grouped into a set.
##
MergeAndGroupRecords := function ( arg )
    local   res,        # merged record, result
            record,     # one of the arguments
            name,       # name of one component of <record>
            set_list;  # keeps track if a set was created for a field

    res := When(arg=[], rec(), arg[1]);
    set_list := [];
    for record  in  arg{[2..Length(arg)]} do
        for name  in UserRecFields( record )  do
            if IsBound(res.(name))  then
                if name in set_list then
                    res.(name) := UnionSet(res.(name), Set([record.(name)]) );
                else
                    res.(name) := UnionSet(Set([res.(name)]), Set([record.(name)]));
                    Add(set_list, name);
                fi;
            else
                res.(name) := record.(name);
            fi;
        od;
    od;
    return res;
end;


Class(CudaCodegen, DefaultCodegen, rec(

    SIMTISum := meth(self, o, y, x, opts) 
        local lcode, simtidx, decls, d, v;

        simtidx := o.simt_dim.simt_idx();
        lcode := simt_loop(simtidx, o.var, o.domain,
            self(o.child(1), y, x, opts));

        # If not a regular loop, add simt index to inner array's parallel context
        if simtidx <> Ignore then
            self.simtidx_rec.(o.var.id) := simtidx;
            decls := Collect(lcode, @(1, decl, d -> ForAny(d.vars, v -> IsArrayT(v.t))));
            for d in decls do
                DoForAll(d.vars, v -> When(IsBound(v.parctx), Add(v.parctx, [o.var, simtidx]), v.setAttrTo("parctx", [ [o.var, simtidx] ])) );
            od;
        fi;

        return When( ObjId(o.simt_dim)=ASIMTKernelFlag, simt_block( lcode ), lcode );
    end,

    SIMTSUM := meth(self, o,y,x,opts)
        local i, ch, numch, code_ch, cch, pb, parb;
        ch    := o.children();
        numch := Length(ch);
        code_ch := chain();

        for i in [1..numch] do
            cch := self(ch[i], y, x, opts);

            if o.simt_dim.need_cond(i) then
                Add(code_ch.cmds, IF(o.simt_dim.simt_cond(i), cch, skip()) );
            else
                Add(code_ch.cmds, cch);
            fi;

        od;

        return code_ch;
    end,

    BB := meth(self,o,y,x,opts) 
        local res;

        res := Inherited(o, y, x, opts);

        # inner temps are unrolled - drop from pre/post tables (See Compose below)
        if opts.mempool then
            self.tarray_pre  := DropLast(self.tarray_pre,  1);
            self.tarray_post := DropLast(self.tarray_post, 1);
            Add(self.tarray_pre,  rec());
            Add(self.tarray_post, rec());
        fi;

        return res;
        
    end,

    Compose := meth(self, o,y,x,opts)
        local ch, numch, vecs, code_ch, get_simt_sync, ta_pre, ta_post, ci, cch, simts, parb;
        ch    := o.children();
        numch := Length(ch);

        # propagate x and y arrays and create temporary arrays
        vecs  := self._composePropagate(ch, y, x, c -> TempArray(y,x,c));

        # order them so that first to be evaluated is first in array.
        vecs := Reversed(vecs);
        ch   := Reversed(ch);
        
        get_simt_sync := (c) -> let(simtss := List( Collect(c, @.cond(e -> IsRec(e) and IsBound(e.simt_dim))), e -> e.simt_dim.simt_sync() ),
                                   When(simtss<>[], Maximum(simtss), skip() ) 
                                );
        
        code_ch := [];

        if opts.mempool then
            ta_pre  := Last(self.tarray_pre);
            ta_post := Last(self.tarray_post);
        fi;

        for ci in [1..numch] do
            if opts.mempool then
                Add(self.tarray_pre,  rec());
                Add(self.tarray_post, rec());
            fi;
            cch := self(ch[ci], vecs[ci+1], vecs[ci], opts);
            # Determine sync primitive at ch's boundary
            simts := get_simt_sync(ch[ci]);
            Append(code_ch, When(ObjId(simts)<>skip, [cch, simts], [cch]));

            if opts.mempool then
                # Add new temps to pre/post tables. 
                # Composition creates a pre/post relationship btw temps.
                if Last(self.tarray_pre) = rec() then
                    ta_pre  := MergeAndGroupRecords(ta_pre,  rec( (vecs[ci+1].id) := Set([vecs[ci]]) ) );
                    ta_post := MergeAndGroupRecords(ta_post, rec( (vecs[ci].id)   := Set([vecs[ci+1]]) ) );
                else
                    ta_pre  := MergeAndGroupRecords(ta_pre,  Last(self.tarray_pre) );
                    ta_post := MergeAndGroupRecords(ta_post, Last(self.tarray_post) );
                fi;
                self.tarray_pre  := DropLast(self.tarray_pre,  1);
                self.tarray_post := DropLast(self.tarray_post, 1);

            fi;
        od;

        # Wrap code in variable declaration.
        return decl(
                Difference(Flat(vecs{[2..Length(vecs)-1]}), Flat([x,y])),
                chain( code_ch )
            );
    end,

    wrap_gpu_timing := function(ker_list, opts)
        local start, stop, ms;
        
        if not opts.gpu_timing then
            return ker_list;
        fi;

        Append(opts.includes, ["<stdio.h>", "<helper_cuda.h>"]);

        start := var.fresh_t("start", T_CudaEvent); 
        stop := var.fresh_t("stop", T_CudaEvent);
        ms    := var.fresh_t("ms", T_Real(32));

        return decl([start, stop, ms],
                    chain(
                        cu_event_create(addrof(start)),
                        cu_event_create(addrof(stop)),
                        cu_check_errors(cu_event_record(start, false)),
                        ker_list,
                        cu_check_errors(cu_event_record(stop, false)),
                        cu_check_errors(cu_event_synchronize(stop, false)),
                        assign(ms, V(0)),
                        cu_event_elapsed_time(addrof(ms), start, stop),
                        #cprintf("SPIRAL-based CUDA execution [ms]:\\t%f\\n", ms),
                        cu_event_destroy(start),
                        cu_event_destroy(stop)
                    )
            );
    end,

    wrap_kernel := meth(self, ker_desc, io, params, o_dims, opts)
        local cp_in, cp_out;
        cp_out := cu_memcpy(var.table.("h"::io[1].id), io[1], o_dims[1], cudaMemcpyDeviceToHost);
        cp_in  := [cu_memcpy(io[2], var.table.("h"::io[2].id), o_dims[2], cudaMemcpyHostToDevice)]
                ::List(params, p -> cu_memcpy(p, var.table.("h"::p.id), p.t.size, cudaMemcpyHostToDevice));

        return decl(Set(List(ker_desc.cuda_kers, kc ->kc.dim_grid))::Set(List(ker_desc.cuda_kers, kc ->kc.dim_block)),
                chain(
                    cp_in,
                    self.wrap_gpu_timing(
                        List(ker_desc.cuda_kers, kc -> ApplyFunc(cu_call,[kc.cuda_ker.id, kc.dim_grid, kc.dim_block]::kc.cuda_ker.params) ),
                        opts),                        
                    cp_out
                ));
    end,

    wrap_kernel_devfunc := meth(self, ker_desc, io, params, o_dims, opts)
        return decl(Set(List(ker_desc.cuda_kers, kc ->kc.dim_grid))::Set(List(ker_desc.cuda_kers, kc ->kc.dim_block)),
                chain(
                        List(ker_desc.cuda_kers, kc -> ApplyFunc(cu_call,[kc.cuda_ker.id, kc.dim_grid, kc.dim_block]::kc.cuda_ker.params) )
                ));
    end,

    get_dim_idx := (self, ker, IdxT) >> let( ll := List(Collect(ker, @(1,simt_loop,l->ObjId(l.simt_idx)=IdxT) ), l->l.simt_idx ), 
                                         When(Length(ll)>0, 
                                            Checked(ForAll(ll, l -> l.size()=ll[1].size()), ll[1].size()), 
                                            V(1)
                                        )),


    _reduce_tarray_graph := function(pre, post, ta_list)
        local ta_id, ta, t, new_pre, new_post;
        new_pre  := Copy(pre);
        new_post := Copy(post);
        # Only consider provided arrays
        for ta_id in UnionSet(UserRecFields(pre), UserRecFields(post)) do
            ta := var.table.(ta_id);
            if not ta in ta_list then
                if IsBound(new_pre.(ta_id)) then
                    for t in new_pre.(ta_id) do
                        new_post.(t.id) := UnionSet( When(IsBound(new_post.(t.id)),  new_post.(t.id),  []), 
                                                     When(IsBound(new_post.(ta_id)), new_post.(ta_id), []) );
                        new_post.(t.id) := Difference(new_post.(t.id), [ta]);
                    od;
                fi;
                if IsBound(new_post.(ta_id)) then
                    for t in new_post.(ta_id) do
                        new_pre.(t.id) := UnionSet( When(IsBound(new_pre.(t.id)),  new_pre.(t.id),  []), 
                                                    When(IsBound(new_pre.(ta_id)), new_pre.(ta_id), []) );
                        new_pre.(t.id) := Difference(new_pre.(t.id), [ta]);
                    od;
                fi;

                if IsBound(new_pre.(ta_id)) then
                    Unbind(new_pre.(ta_id));
                fi;
                if IsBound(new_post.(ta_id)) then
                    Unbind(new_post.(ta_id));
                fi;
            fi;
        od;

        return [new_pre, new_post];
    end,

    _next_color := function(i, e, exclude)
        local c;
        c := i;
        while c<=e and c in exclude do
            c := c+1;
        od;

        return c;
    end,

    _simple_coloring := meth(self, pre, post, taken)
        local q, x, y, ta, locked, res, id_set, id_cnt, col, parb, tas_on_altb;
        
        id_set := UnionSet(UserRecFields(pre), UserRecFields(post));
        id_cnt := Length(id_set);

        x := List(Filtered(id_set, v -> not IsBound(pre.(v))),  vid -> var.table.(vid) );
        y := List(Filtered(id_set, v -> not IsBound(post.(v))), vid -> var.table.(vid) );

        res := Copy(taken);
        locked := Set(List(UserRecFields(taken), v -> taken.(v)));
        q := Filtered( Flat(List(x, v -> post.(v.id))), v -> not v in y and not IsBound(taken.(v.id)) );

        while q <> [] do
            [ta, q] := SplitAt(q, 1);
            ta := ta[1];
            col := self._next_color(1, id_cnt, locked
                                                ::List(Filtered(pre.(ta.id), t -> IsBound(res.(t.id)) ), v -> res.(v.id)) 
                        );
            res.(ta.id) := col;

            #Setup next iteration
            if IsBound(post.(ta.id)) and ForAll(Flat( List(post.(ta.id), p -> pre.(p.id) ) ), 
                                            v -> IsBound(res.(v.id))) then
                    # push on queue
                    q := Filtered(post.(ta.id), p -> not p in y)::q;
            fi;
            # else do nothing - still need to complete other par. branches

            if Length(pre.(ta.id)) > 1 then
                #Unlock color of previous divergent point
                locked := DropLast(locked, 1);
            fi;
            if IsBound(post.(ta.id)) and Length(post.(ta.id)) > 1 then
                Add(locked, col);
            fi;

        od;

        return res;
    end,

    _map_col2mem := function(coloring, decl_specs)
        local c, p, ta, cols, samecol_tas, ta2mem, mem_list;

        cols := Set(Flat(List(UserRecFields(coloring), v -> coloring.(v))));
        ta2mem := rec();
        mem_list := [];
        for c in cols do
            samecol_tas := List(Filtered(UserRecFields(coloring), v -> c = coloring.(v)), vid -> var.table.(vid));
            p := var.fresh_t("P", TArray(samecol_tas[1].t.t, Maximum(List(samecol_tas, v -> v.t.size))) );
            p.("decl_specs") := decl_specs;
            for ta in samecol_tas do
                ta2mem.(ta.id) := p;
            od;
            Add(mem_list, p);
        od;

        return [ta2mem, mem_list];
    end,

    compact_arrays := meth(self, ker, ta_list, ker_args, decl_specs, opts)
        local cross_ker_tas, pre, post, ck_pre, ck_post, ck_col, coloring, ta2mem;

        #Currently limited to coloring cross-kernel tas
        cross_ker_tas := Filtered(ta_list, v -> IsBound(v.crossker) and v.crossker);
        ta_list := Difference(ta_list, cross_ker_tas);
        [ck_pre, ck_post] := self._reduce_tarray_graph(self.tarray_pre, self.tarray_post, cross_ker_tas::ker_args);
        ck_col := self._simple_coloring(ck_pre, ck_post, rec());
        #assign mem areas based on coloring
        [ta2mem, cross_ker_tas] := self._map_col2mem(ck_col, decl_specs);
        ker := SubstVars(ker, ta2mem);
        
        return [ker, cross_ker_tas::ta_list];
    end,

    extract_tarrays := meth(self, ker, cond, opts)
        local decls, d, ta, tarrays;

        decls := Collect(ker, @(1, decl, d -> ForAny(d.vars, v -> IsArrayT(v.t)) ) );
        
        tarrays := [];
        for d in decls do
            # Collect temp arrays based on cond
            ta := Filtered(d.vars, v -> cond(v) );
            d.vars := Difference(d.vars, ta);

            Append(tarrays, ta);
        od;

        return tarrays;
    end,

    to_grid_arrays := meth(self, ker, ta_list, ker_args, opts)
        local ta, idx_list, blk_ids, th_ids, idx, idx_cnt, idx_rng, derefs, nths, v;

        for ta in ta_list do
            ta.("decl_specs") := ["__device__"];
            idx_list := When(IsBound(ta.parctx), ta.parctx, []);
            #parctx format: [ [loopvar1, simtIdx1], ... ]
            blk_ids := Filtered(idx_list, idx -> IsSimtBlockIdx(idx[2])); Sort(blk_ids, (i1, i2) -> i1[2].name < i2[2].name);
            th_ids  := Filtered(idx_list, idx -> IsSimtThreadIdx(idx[2])); Sort(th_ids, (i1, i2) -> i1[2].name < i2[2].name);
            for idx in th_ids::blk_ids do
                idx_cnt := idx[2].count(); # Num of threads associated with index
                if idx_cnt > 1 then
                    idx_rng := idx[2].get_rng(); # Thread range: [<1st tid>, <last tid>]
                    derefs := Collect(ker, @(1, deref, v -> ta in v.free()));
                    nths   := Collect(ker, @(1,   nth, v -> ta in v.free()));

                    for v in derefs do
                        v.loc := add(v.loc, ta.t.size*(idx[2]-idx_rng[1]) );
                    od;
                    for v in nths do
                        v.idx := add(v.idx, ta.t.size*(idx[2]-idx_rng[1]));
                    od;
                    ta.t.size := ta.t.size*idx_cnt;
                fi;
            od;
        od;

        if opts.mempool then
            [ker, ta_list] := self.compact_arrays(ker, ta_list, ker_args, ["__device__"], opts);
        fi;

        return [ker, ta_list];
    end,

    to_block_shmem_arrays := meth(self, ker, ta_list, ker_args, opts)
        local ta, idx_list, blk_ids, th_ids, idx, idx_cnt, idx_rng, derefs, nths, size, padded, v;

        for ta in ta_list do
            padded := false;
            ta.("decl_specs") := ["__shared__"];
            idx_list := When(IsBound(ta.parctx), ta.parctx, []);
            th_ids  := Filtered(idx_list, idx -> IsSimtThreadIdx(idx[2])); Sort(th_ids, (i1, i2) -> i1[2].name < i2[2].name);
            for idx in th_ids do
                idx_cnt := idx[2].count();
                if idx_cnt > 1 then
                    size := ta.t.size;
                    if not padded and Mod(size, 2) = 0 then
                        size := size+1;
                    fi;
                    padded := true;
                    idx_rng := idx[2].get_rng();
                    derefs := Collect(ker, @(1, deref, v -> ta in v.free()));
                    nths   := Collect(ker, @(1,   nth, v -> ta in v.free()));

                    for v in derefs do
                        v.loc := add(v.loc, size*(idx[2]-idx_rng[1]) );
                    od;
                    for v in nths do
                        v.idx := add(v.idx, size*(idx[2]-idx_rng[1]));
                    od;
                    ta.t.size := size*idx_cnt;
                fi;
            od;
        od;

        ker := decl(ta_list, ker);

        return [ker, ta_list];
    end,

    extract_ker_datas := meth(self, cuda_icode, opts)
        local ker_datas, tcuicode, d;

        ker_datas := List(Collect(cuda_icode, data), d -> d.var);

        tcuicode := SubstTopDown(cuda_icode, data, e -> e.cmd);
        while tcuicode <> cuda_icode do
            cuda_icode := tcuicode;
            tcuicode := SubstTopDown(cuda_icode, data, e -> e.cmd);
        od;

        return [cuda_icode, ker_datas];
    end,

    _get_data_loopindex_deps := function(icode, d, opts)
        local ln, fv, la, li, lv, locli;
        ln := Collect(icode, @(1, nth).cond(v -> d in v.loc.free()));
        fv := Set( Flat(List(ln, v -> v.idx.free())) );
        li := Filtered(fv, v -> IsLoopIndex(v));

        #If code in SSA form using lv set to avoid cyclic deps could be avoided
        fv := Difference(fv, li); lv := Copy(fv);
        while(fv <> []) do
            la := Collect(icode, @(1, assign).cond(a -> a.loc in fv));
            fv := Set( Flat(List(la, a -> a.exp.free())) );
            locli := Filtered(fv, v -> IsLoopIndex(v));
            fv := Difference(fv, locli);
            fv := Difference(fv, lv);
            li := UnionSet(li, locli);
            lv := UnionSet(lv, fv);
        od;

        return li;
    end,

    ker_datas_to_device := meth(self, ker_datas, cuda_icode, opts)
        local d, li;

        for d in Reversed(ker_datas) do
            li := self._get_data_loopindex_deps(cuda_icode, d, opts);
            # If any warp-divergent access then allocate in dev mem otherwise constant.
            if ForAny(li, v -> IsBound(self.simtidx_rec.(v.id)) 
                                and ObjId(self.simtidx_rec.(v.id)) = simtThreadIdxX) then
                d.("decl_specs") := ["__device__"];
            else
                d.("decl_specs") := ["__constant__"];
            fi;
            cuda_icode := data(d, d.value, cuda_icode);
        od;

        return cuda_icode;
    end,

    make_kernels := meth(self, full_kernel, device_data, full_args, opts)
        local kercx, ker_cnt, ker, ker_args, ker_datas, cuda_ker, cuda_desc, cuda_icode, cuda_sub, 
                dim_grid, dim_block, tbody, tas_grid, tas_block_shmem, cross_ker_tas, ta;
				
		cuda_sub := Cond(IsBound(opts.cudasubName), Concat("ker_",opts.cudasubName), "ker_code");

        cuda_desc := rec(grid_tarrays := [], cuda_kers := [] );

        [full_kernel, ker_datas] := self.extract_ker_datas(full_kernel, opts);
        
        # Mark cross kernel temporaries
        cross_ker_tas := Filtered(Flat(List(Collect(full_kernel, @@(1, decl, (d, ctx) -> not IsBound(ctx.simt_block) or ctx.simt_block = [] )),
                            d -> d.vars)), v -> IsArrayT(v.t));
        DoForAll(cross_ker_tas, v -> v.setAttrTo("crossker", true));
        #Extract all temp arrays that should map to dev mem 
        tas_grid := self.extract_tarrays(full_kernel, 
                                            When(opts.use_shmem,
                                                    v -> (IsBound(v.crossker) and v.crossker) or (IsBound(v.t.size) and (v.t.size >= opts.max_shmem_size/8/2)),
                                                    True
                                            ), opts);
        #Allocate in dev mem 
        [full_kernel, tas_grid] := self.to_grid_arrays(full_kernel, tas_grid, full_args, opts);
        Append(cuda_desc.grid_tarrays, tas_grid);

        kercx := Collect(full_kernel, simt_block);
        kercx := When(kercx = [], [ full_kernel ], kercx);
        ker_cnt := 0;
        for ker in kercx do
            
            tbody := When(ObjId(ker) = simt_block, chain(ker.cmds), ker);
            ker_args := Intersection(device_data, tbody.free())::Intersection(full_args, tbody.free());
            #Extract remaining shared mem temp arrays if required 
            tas_block_shmem := self.extract_tarrays(tbody, v -> opts.use_shmem, opts);
            #Allocate in shared mem 
            [tbody, tas_block_shmem] := self.to_block_shmem_arrays(tbody, tas_block_shmem, ker_args, opts);

            dim_grid := var.fresh_t_obj("g", Dim3(), rec( x := self.get_dim_idx(tbody, simtBlockIdxX), 
                                                          y := self.get_dim_idx(tbody, simtBlockIdxY), 
                                                          z := self.get_dim_idx(tbody, simtBlockIdxZ)
                                                        ) );
            dim_block := var.fresh_t_obj("b", Dim3(), rec( x := self.get_dim_idx(tbody, simtThreadIdxX), 
                                                           y := self.get_dim_idx(tbody, simtThreadIdxY), 
                                                           z := self.get_dim_idx(tbody, simtThreadIdxZ)
                                                        ) );

            cuda_ker := specifiers_func(["__global__"], TVoid, cuda_sub::StringInt(ker_cnt), Filtered(ker_args, d -> not IsBound(d.("decl_specs")) or not "__constant__" in d.("decl_specs")), tbody );

            Add(cuda_desc.cuda_kers,  rec(dim_grid := dim_grid, dim_block := dim_block, cuda_ker := cuda_ker));

            ker_cnt := ker_cnt + 1;
        od;

        cuda_icode := chain(List(cuda_desc.cuda_kers, ck -> ck.cuda_ker));
        cuda_icode := self.ker_datas_to_device(ker_datas, cuda_icode, opts);

        return [cuda_desc, cuda_icode];

    end,

    make_init := meth(self, initname, initparams, init_datas, device_datas, cuda_desc, io, params, o_dims, opts)
        local d, dd, t_id, t_var, tarrays, init_chain, init_func;

        # Use the generated init for the host arrays
        for d in init_datas do
            t_var := d.var;
            d.var := t_var.clone();
            t_id := d.var.id;
            d.var.id := "h"::t_var.id;
            d.init := SubstVars(d.init, rec((t_var.id) := d.var));
            Unbind(var.table.(t_id));
            var.table.(d.var.id) := d.var;
        od;

        init_chain := chain(List(device_datas, dd ->    When(IsBound(dd.("decl_specs")) and "__constant__" in dd.("decl_specs"),
                                                            chain(SReduce(dd.init, opts),
                                                                cu_memcpy_to_sym(dd, var.table.("h"::dd.id), dd.t.size)
                                                                ),
                                                            chain(cu_allocate(dd, dd.t.t, dd.t.size), 
                                                                SReduce(dd.init, opts), 
                                                                cu_memcpy(dd, var.table.("h"::dd.id), dd.t.size, cudaMemcpyHostToDevice)
                                                                )
                                                        )
                                )
                                ::When(not (IsBound(opts.devFunc) and opts.devFunc), List(params, dd -> cu_allocate(dd, dd.t.t, dd.t.size) ), []) 
                            );
        if not (IsBound(opts.devFunc) and opts.devFunc) then
            for i in [1..Length(io)] do
                Add(init_chain.cmds, cu_allocate(io[i], io[i].t.t, o_dims[i]));
            od;
        fi;

        for d in cuda_desc.devmem do
            Add(init_chain.cmds, cu_allocate(d.var, d.t, d.n));
        od;

        init_func := func(TVoid, initname, Set(Collect(init_chain, param)), init_chain);
        return init_func;
    end,

    make_destroy := meth(self, destroyname, init_datas, device_datas, cuda_desc, io, params, opts)
        local destroy_chain, destroy_func;

        destroy_chain := chain( List(Filtered(device_datas, dd -> not IsBound(dd.("decl_specs")) or not "__constant__" in dd.("decl_specs") ), 
                                    d -> cu_free(d))
                                ::When(not (IsBound(opts.devFunc) and opts.devFunc), List(params, d -> cu_free(d)), [])
                                ::When(IsBound(opts.devFunc) and opts.devFunc, [], List(io, d -> cu_free(d)))
                                ::List(cuda_desc.devmem, d->cu_free(d.var)));

        destroy_func := func(TVoid, destroyname, Set(Collect(destroy_chain, param)), destroy_chain);
        return destroy_func;
    end,

    assemble_prog := meth(self, datas, initparams, params, io, o, icode, opts)
        local hparams, hio, p, hp, init_datas, device_datas, ker_args,
              sub, initsub, destroysub,
              cuda_desc, cuda_icode, icode_wrap, initcode, destroycode, prog,
              wrapk_f, devmem, vr;

        wrapk_f := When(IsBound(opts.devFunc) and opts.devFunc, self.wrap_kernel_devfunc, self.wrap_kernel);
        devmem := [];
        
        hparams := [];
        for p in params do 
            p.setAttr("decl_as_ptr");
            hp := p.clone(); 
            Unbind(var.table.(hp.id));
            hp.id := When(IsBound(opts.devFunc) and opts.devFunc, p.id, "h"::p.id);
            var.table.(hp.id) := hp;
            Add(hparams, hp);
        od;

        hio := [];
        
        if not (IsBound(opts.devFunc) and opts.devFunc) then
            for p in io do 
                hp := p.clone();
                Unbind(var.table.(hp.id));
                hp.id := "h"::p.id;
                var.table.(hp.id) := hp;
                Add(hio, hp);
            od;
        fi;
        
        # Device data here refers to data initialized in init function and therefor residing in dev mem
        init_datas := Filtered(datas, e -> IsBound(e.var.init));
        device_datas := List(init_datas, d -> d.var);

        sub := Cond(IsBound(opts.subName), opts.subName, "transform");
        initsub := Cond(IsBound(opts.subName), Concat("init_", opts.subName), "init");
        destroysub := Cond(IsBound(opts.subName), Concat("destroy_", opts.subName), "destroy");
        ker_args := Concatenation(io, params);

        [cuda_desc, cuda_icode] := self.make_kernels(icode, device_datas, ker_args, opts);

        cuda_desc.devmem := [];
        if IsBound(opts.dynamicDeviceMemory) and opts.dynamicDeviceMemory then
            devmem := List(cuda_desc.grid_tarrays, d-> rec(t := TPtr(d.t.t), n := d.t.size, id := d.id, var := var.fresh_t("Q", TPtr(d.t.t))));
            cuda_icode := SubstVars(cuda_icode, FoldR(devmem, (a,b) -> CopyFields(a, rec((b.id) := b.var)), rec()));
            cuda_desc.grid_tarrays := List(devmem, d->d.var);
            cuda_desc.devmem := devmem;
        fi;

        icode_wrap := func(TVoid, sub, Concatenation(When(IsBound(opts.devFunc) and opts.devFunc, io, hio), hparams), chain(wrapk_f(self, cuda_desc, io, params, o.dimensions, opts)));
        if IsBound(opts.generateInitFunc) and opts.generateInitFunc then
            initcode := self.make_init(initsub, initparams, init_datas, device_datas, cuda_desc, io, params, o.dimensions, opts);
            destroycode := self.make_destroy(destroysub, init_datas, device_datas, cuda_desc, io, params, opts);
            prog := program(
                decl(List(datas, x->x.var)::cuda_desc.grid_tarrays::device_datas::params::When(IsBound(opts.devFunc) and opts.devFunc, [], io),
                    chain(
                        initcode, 
                        cuda_icode,
                        icode_wrap,
                        destroycode
                    )));
        else
            initcode := self.make_init(initsub, initparams, init_datas, device_datas, cuda_desc, io, params, o.dimensions, opts);
            destroycode := self.make_destroy(destroysub, init_datas, device_datas, cuda_desc, io, params, opts);
            prog := program(
                decl(cuda_desc.grid_tarrays::params::When(IsBound(opts.devFunc) and opts.devFunc, [], io),
                    chain(
                        initcode, 
                        cuda_icode,
                        icode_wrap,
                        destroycode
                    )));
        fi;

        return prog;
    end,

    Formula := meth(self, o, y, x, opts)
        local icode, icode1, datas, prog, initparams, params, io, t, o, field;
        
        o := SumsUnification(o.child(1), opts);

        [x, y] := self.initXY(x, y, opts);

        io := When(x=y, [x], [y, x]);
        io := io::When(IsBound(opts.Xptr), [opts.Xptr], []);
        io := io::When(IsBound(opts.Yptr), [opts.Yptr], []);
        
        params := Set(Concatenation(Collect(o, param), Filtered(Collect(o, var), IsParallelLoopIndex)));

        if opts.mempool then
            self.tarray_pre  := [rec()];
            self.tarray_post := [rec()];
        fi;
        self.simtidx_rec := rec();

        datas := Collect(o, FDataOfs);
        [o,t] := UTimedAction(BlockSumsOpts(o, opts)); #PrintLine("BlockSums ", t);
        [icode,t] := UTimedAction(self(o, y, x, opts)); #PrintLine("codegen ", t);

        if opts.mempool then
            self.tarray_pre := self.tarray_pre[1];
            self.tarray_post := self.tarray_post[1];
            for field in Difference(UserRecFields(self.tarray_pre), List(io, v -> v.id)) do
                self.tarray_pre.(field)  := Set(Flat(self.tarray_pre.(field)));
                self.tarray_post.(field) := Set(Flat(self.tarray_post.(field)));
            od;
            for field in List(io, v -> v.id) do
                if IsBound(self.tarray_pre.(field)) then
                    self.tarray_pre.(field)  := Set(Flat(self.tarray_pre.(field)));
                fi;
                if IsBound(self.tarray_post.(field)) then
                    self.tarray_post.(field) := Set(Flat(self.tarray_post.(field)));
                fi;
            od;

        fi;

        icode := RemoveAssignAcc(icode);
        Unbind(Compile.times);
        [icode,t] := UTimedAction(BlockUnroll(icode, opts)); #PrintLine("BlockUnroll ", t);
        icode := DeclareHidden(icode);
        if IsBound(opts.isFixedPoint) and opts.isFixedPoint then
            icode := FixedPointCode(icode, opts.bits, opts.fracbits);
        fi;

        if IsBound(opts.postCompileStrategy) then
            icode := opts.postCompileStrategy(icode, opts);
        fi;

        initparams := Copy(params);
        if IsBound(opts.symbol) then
          params := Concatenation(params, opts.symbol);
        fi;

        if IsBound(opts.accStrategy) then
          icode.iy := y;
          icode.iy.n := o.dims()[1];
          icode.ix := x;
          icode.ix.n := o.dims()[2];
          icode.ivars := Concatenation(params, List(datas, x->x.var));
          icode := opts.accStrategy(icode);
        fi;

        prog := self.assemble_prog(datas, initparams, params, io, o, icode, opts);
        prog.dimensions := o.dims();
        return prog;
    end,
    ));
