Class(cu_allocate_managed, assign);

cudaMemcpyHostToHost     := "cudaMemcpyHostToHost";
cudaMemcpyHostToDevice   := "cudaMemcpyHostToDevice";
cudaMemcpyDeviceToHost   := "cudaMemcpyDeviceToHost";
cudaMemcpyDeviceToDevice := "cudaMemcpyDeviceToDevice";

Class(cu_check_errors, call);

Class(T_Class, T_Type, rec(
    
    fields := rec(),

    updateParams := meth(self)
        Constraint(IsString(self.params[1]));
        Constraint(When(Length(self.params)>1, IsRec(self.params[2]), true));
    end,
));


Class(Dim3, T_Class, rec(

    __call__ := (self) >> let(fields := rec(x := TUInt, y := TUInt, z := TUInt), Inherited("Dim3", fields)),    

    )
);

var.("fresh_t_obj") := meth(self,id,t,params) 
    local v, f;
    if IsType(t) and IsRec(params) and ForAll(RecFields(params), f->f in RecFields(t.params[2])) then
        v := var.fresh_t(id, t);
        for f in Filtered(RecFields(params), e -> IsType(t.params[2].(e))) do 
            v.(f) := var.fresh_t(f, t.params[2].(f));
            v.(f).setValue(params.(f));
        od;
        return v;
    else
        Error("<t> must be a type or an integer that represents an interval");
    fi;
end;

Class(T_CudaEvent, T_Type);
Class(cu_event_create, call);
Class(cu_event_record, call);
Class(cu_event_destroy, call);
Class(cu_event_synchronize, call);
Class(cu_device_synchronize, call);
Class(cu_event_elapsed_time, call);

Class(cu_allocate, assign, rec(
   isAssign := true,
   __call__ := (self, loc, type, size) >> WithBases(self,
       rec(operations := CmdOps,
       loc  := toAssignTarget(loc),
       type  := type,
       size := size)
       ),

   rChildren := self >> [self.loc, self.type, self.size],
   rSetChild := rSetChildFields("loc", "type", "size"),

   print := (self,i,si) >> let(name := Cond(IsBound(self.isCompute) and self.isCompute,
                                            gap.colors.DarkYellow(self.__name__),
                                            IsBound(self.isLoad) and self.isLoad,
                                            gap.colors.DarkRed(self.__name__),
                                            IsBound(self.isStore) and self.isStore,
                                            gap.colors.DarkGreen(self.__name__),
                                            self.__name__),
                                Print(name, "(", self.loc, ", ", self.type, ", ", self.size, ")"))
));

Class(cu_memcpy, assign, rec(
   isAssign := true,
   __call__ := (self, loc, exp, size, kind) >> WithBases(self,
       rec(operations := CmdOps,
       loc  := toAssignTarget(loc),
       exp  := toExpArg(exp),
       size := size,
       kind := kind)),

   rChildren := self >> [self.loc, self.exp, self.size, self.kind],
   rSetChild := rSetChildFields("loc", "exp", "size", "kind"),

   print := (self,i,si) >> let(name := Cond(IsBound(self.isCompute) and self.isCompute,
                                            gap.colors.DarkYellow(self.__name__),
                                            IsBound(self.isLoad) and self.isLoad,
                                            gap.colors.DarkRed(self.__name__),
                                            IsBound(self.isStore) and self.isStore,
                                            gap.colors.DarkGreen(self.__name__),
                                            self.__name__),
                                Print(name, "(", self.loc, ", ", self.exp, ", ", self.size, ", ", self.kind, ")"))
));

Class(cu_memcpy_to_sym, assign, rec(
   isAssign := true,
   __call__ := (self, loc, exp, size) >> WithBases(self,
       rec(operations := CmdOps,
       loc  := toAssignTarget(loc),
       exp  := toExpArg(exp),
       size := size)),

   rChildren := self >> [self.loc, self.exp, self.size],
   rSetChild := rSetChildFields("loc", "exp", "size"),

   print := (self,i,si) >> let(name := Cond(IsBound(self.isCompute) and self.isCompute,
                                            gap.colors.DarkYellow(self.__name__),
                                            IsBound(self.isLoad) and self.isLoad,
                                            gap.colors.DarkRed(self.__name__),
                                            IsBound(self.isStore) and self.isStore,
                                            gap.colors.DarkGreen(self.__name__),
                                            self.__name__),
                                Print(name, "(", self.loc, ", ", self.exp, ", ", self.size, ")"))
));

Class(cu_free, call);

Class(cu_call, call, rec(
    __call__ := arg >> let(
        len := Length(arg),
        self := arg[1],
        f := arg[2],
        dim_grid := Checked(IsList(arg[3]) or IsVar(arg[3]), arg[3]),
        dim_block := Checked(IsList(arg[4]) or IsVar(arg[4]), arg[4]),
        args := arg{[5..len]},
        WithBases(self, rec(
            func := f,
            dim_grid := dim_grid,
            dim_block := dim_block,
            operations := CmdOps,
            args := List(args, toExpArg)))
        ),

    rChildren := self >> [self.func, self.dim_grid, self.dim_block]::self.args,
    
    rSetChild := meth(self, n, newChild)
        local len;
        len := Length(self.args);
        if n > len+3 then Error(); fi;
        if n = 1 then
            self.func := newChild;
        elif n = 2 then
            self.dim_grid := newChild;
        elif n = 3 then
            self.dim_block := newChild;
        elif n > 3 and n <= len+3 then
            self.args[n-3] := newChild;
        fi;
    end,

    print := (self,i,si) >> Print(self.func, "<<<", self.dim_grid, ",", self.dim_block, ">>>", "(", PrintCS(self.args), ")")

));
