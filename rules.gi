# Extension of RulesRC/Sums/Diag to SIMT operators.

RewriteRules(RulesRC, rec(
    RC_SIMTISum := Rule([RC, @(1, SIMTISum)], e -> SIMTISum(@(1).val.simt_dim, @(1).val.var, @(1).val.domain, RC(@(1).val.child(1)))),
     RC_SIMTSUM := Rule([RC, @(1, SIMTSUM)], e -> SIMTSUM(@(1).val.simt_dim, List(@(1).val.children(), RC)))        
    ));


RewriteRules(RulesSums, rec(
    SIMTSUMAssoc := ARule( SIMTSUM, [ @(1,SIMTSUM) ],  
                            function(e) # Substitute rngs from inner SIMTSUM in simt_dim
                                local pos;

                                pos := Position(e.children(), @(1).val);
                                e.simt_dim := e.simt_dim.update_simt_range(pos, @(1).val.simt_dim);
                                return @(1).val.children();
                            end ),
    
    PullInRightSIMTSums := ARule( Compose,
            [ @(1, [Prm, Scat, ScatAcc, TCast, PushR, PushLR, Conj, ConjL, ConjR, ConjLR, FormatPrm]),
              @(2, [SIMTISum, SIMTSUM]) ],
              e -> [ CopyFields(@(2).val, rec(
                        _children :=  List(@(2).val._children, c -> @(1).val * c),
                        dimensions := [Rows(@(1).val), Cols(@(2).val)] )) ]),

    PullInLeftSIMTSums := ARule( Compose,
           [ @(1, [SIMTISum, SIMTSUM]),
             @(2, [Prm, Gath, TCast, PushL, PushLR, Conj, ConjL, ConjR, ConjLR, FormatPrm]) ],
             e -> [ CopyFields(@(1).val, rec(
                    _children := List(@(1).val._children, c -> c * @(2).val),
                    dimensions := [Rows(@(1).val), Cols(@(2).val)] )) ]),
    ));

RewriteRules(RulesDiag, rec(
    DiagSIMTISumLeft := ARule( Compose,
           [ @(1, SIMTISum, canReorder), @(2, RightPull) ],
      e -> [ SIMTISum(@1.val.simt_dim, @1.val.var, @1.val.domain, @1.val.child(1) * @2.val).attrs(@(1).val) ]),

    DiagSIMTISumRight := ARule( Compose,
             [ @(1, LeftPull), @(2, SIMTISum, canReorder) ],
        e -> [ SIMTISum(@2.val.simt_dim, @2.val.var, @2.val.domain, @1.val * @2.val.child(1)).attrs(@(2).val) ]),

     DiagSIMTSUMPullInRight := ARule( Compose,
           [ @(1, LeftPull), @(2, SIMTSUM) ],
      e -> [ ApplyFunc(ObjId(@2.val), [@2.val.simt_dim]::List(@2.val.children(), c -> @1.val * c)) ]),

     DiagSIMTSUMPullInLeft  := ARule( Compose,
           [ @(1, SIMTSUM), @(2, RightPull) ],
      e -> [ ApplyFunc(ObjId(@1.val), [@1.val.simt_dim]::List(@1.val.children(), c -> c * @2.val)) ]),

    ));

RewriteRules(RulesDiagStandalone, rec(
    # Gath * SIMTIDirSum
    CommuteGathSIMTIDirSum := ARule( Compose,
            [ [@(1, Gath), [@(3,fTensor), ..., [fId,@(2)]]],
              [@(0, [PushL, PushLR]), @(4, SIMTIDirSum, e -> (@(2).val mod Rows(e.child(1))) = 0)] 
            ],
            e -> let(
                    ch := DropLast(@(3).val.children(), 1),
                    ratio := @(2).val / Rows(@(4).val.child(1)),
                    f := When(ratio=1, fTensor(ch), fTensor(Concatenation(ch, [fId(ratio)]))),
                    simt_dim := @(4).val.simt_dim,
                    j := @(4).val.var,
                    jj := Ind(f.domain()),

                    [ ObjId(@(0).val)(SIMTIDirSum(simt_dim, jj,      #SubstVars(@(4).val.child(1), rec((j.id) := f.at(jj)))),
                        Data(j, f.at(jj), SubstTopDown(@(4).val.child(1), @(5,fBase,e->e.params[2]=j),
                                                e -> fCompose(f, fBase(jj)))))),
                        @(1).val ]
                )
    ),

    # SIMTIDirSum * Scat
    CommuteSIMTIDirSumScat := ARule( Compose,
            [ [@(0,[PushR, PushLR]), @(4, SIMTIDirSum)],
              [@(1, Scat), [@(3,fTensor), ..., [fId,@(2).cond(e -> (e mod Cols(@(4).val.child(1))) = 0)]]]
            ],

            e -> let(
                    ch := DropLast(@(3).val.children(), 1),
                    ratio := @(2).val / Cols(@(4).val.child(1)),
                    f := When(ratio=1, fTensor(ch), fTensor(Concatenation(ch, [fId(ratio)]))),
                    simt_dim := @(4).val.simt_dim,
                    j := @(4).val.var,
                    jj := Ind(f.domain()),

                   [ @(1).val,
                     ObjId(@(0).val)(SIMTIDirSum(simt_dim, jj,      #SubstVars(@(4).val.child(1), rec((j.id) := f.at(jj)))),
                           Data(j, f.at(jj), SubstTopDown(@(4).val.child(1), @(5,fBase,e->e.params[2]=j),
                                               e -> fCompose(f, fBase(jj)))))) ]
                )
    ),

));
