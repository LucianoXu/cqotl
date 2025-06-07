let obligation1 = { 
  Prover.env =
  [Ast.Definition {name = "Lemma4";
     t =
     Ast.Fun {head = "FORALL";
       args =
       [(Ast.Symbol "a");
         Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "BIT")]};
         Ast.Fun {head = "FORALL";
           args =
           [(Ast.Symbol "q");
             Ast.Fun {head = "QREG"; args = [(Ast.Symbol "BIT")]};
             Ast.Fun {head = "FORALL";
               args =
               [(Ast.Symbol "H");
                 Ast.Fun {head = "EQ";
                   args = [(Ast.Symbol "a"); (Ast.Symbol "true")]};
                 Ast.Fun {head = "ENTAILMENT";
                   args =
                   [Ast.Fun {head = "GUARDED";
                      args =
                      [(Ast.Symbol "a");
                        Ast.Fun {head = "SUBSCRIPT";
                          args =
                          [Ast.Fun {head = "ZEROO";
                             args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                            Ast.Fun {head = "PAIR";
                              args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                            ]}
                        ]};
                     Ast.Fun {head = "SUBSCRIPT";
                       args =
                       [Ast.Fun {head = "ZEROO";
                          args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                         Ast.Fun {head = "PAIR";
                           args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                         ]}
                     ]}
                 ]}
             ]}
         ]};
     e = Ast.Opaque};
    Ast.Definition {name = "Lemma3";
      t =
      Ast.Fun {head = "FORALL";
        args =
        [(Ast.Symbol "a");
          Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "BIT")]};
          Ast.Fun {head = "FORALL";
            args =
            [(Ast.Symbol "b");
              Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "BIT")]};
              Ast.Fun {head = "FORALL";
                args =
                [(Ast.Symbol "q");
                  Ast.Fun {head = "QREG"; args = [(Ast.Symbol "BIT")]};
                  Ast.Fun {head = "FORALL";
                    args =
                    [(Ast.Symbol "H");
                      Ast.Fun {head = "EQ";
                        args =
                        [Ast.Fun {head = "IMPLY";
                           args = [(Ast.Symbol "a"); (Ast.Symbol "b")]};
                          (Ast.Symbol "true")]};
                      Ast.Fun {head = "ENTAILMENT";
                        args =
                        [Ast.Fun {head = "IMPLY";
                           args =
                           [Ast.Fun {head = "NOT"; args = [(Ast.Symbol "a")]};
                             Ast.Fun {head = "SUBSCRIPT";
                               args =
                               [Ast.Fun {head = "ZEROO";
                                  args =
                                  [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                                 Ast.Fun {head = "PAIR";
                                   args =
                                   [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                                 ]}
                             ]};
                          Ast.Fun {head = "IMPLY";
                            args =
                            [Ast.Fun {head = "NOT"; args = [(Ast.Symbol "b")]};
                              Ast.Fun {head = "SUBSCRIPT";
                                args =
                                [Ast.Fun {head = "ZEROO";
                                   args =
                                   [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                                  Ast.Fun {head = "PAIR";
                                    args =
                                    [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                                  ]}
                              ]}
                          ]}
                      ]}
                  ]}
              ]}
          ]};
      e = Ast.Opaque};
    Ast.Definition {name = "Lemma2";
      t =
      Ast.Fun {head = "FORALL";
        args =
        [(Ast.Symbol "x");
          Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "BIT")]};
          Ast.Fun {head = "FORALL";
            args =
            [(Ast.Symbol "H");
              Ast.Fun {head = "EQ";
                args =
                [Ast.Fun {head = "NOT"; args = [(Ast.Symbol "x")]};
                  (Ast.Symbol "true")]};
              Ast.Fun {head = "EQ";
                args = [(Ast.Symbol "x"); (Ast.Symbol "false")]}
              ]}
          ]};
      e = Ast.Opaque};
    Ast.Definition {name = "Lemma1";
      t =
      Ast.Fun {head = "FORALL";
        args =
        [(Ast.Symbol "x");
          Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "BIT")]};
          Ast.Fun {head = "EQ";
            args =
            [Ast.Fun {head = "NOT";
               args = [Ast.Fun {head = "NOT"; args = [(Ast.Symbol "x")]}]};
              (Ast.Symbol "x")]}
          ]};
      e = Ast.Opaque};
    Ast.Assumption {name = "iADD";
      t =
      Ast.Fun {head = "FORALL";
        args =
        [(Ast.Symbol "i");
          Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]};
          Ast.Fun {head = "FORALL";
            args =
            [(Ast.Symbol "j");
              Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "BIT")]};
              Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]}]}
          ]}};
    Ast.Assumption {name = "lt";
      t =
      Ast.Fun {head = "FORALL";
        args =
        [(Ast.Symbol "i");
          Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]};
          Ast.Fun {head = "FORALL";
            args =
            [(Ast.Symbol "j");
              Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]};
              Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "BIT")]}]}
          ]}};
    Ast.Assumption {name = "miu";
      t = Ast.Fun {head = "PDIST"; args = [(Ast.Symbol "BIT")]}};
    Ast.Assumption {name = "P1";
      t =
      Ast.Fun {head = "OTYPE";
        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]}};
    Ast.Assumption {name = "P0";
      t =
      Ast.Fun {head = "OTYPE";
        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]}};
    Ast.Assumption {name = "vplus";
      t = Ast.Fun {head = "KTYPE"; args = [(Ast.Symbol "BIT")]}};
    Ast.Assumption {name = "H";
      t =
      Ast.Fun {head = "OTYPE";
        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]}}
    ];
  proof_name = "WrappedPf1";
  proof_prop =
  Ast.Fun {head = "FORALL";
    args =
    [(Ast.Symbol "n"); Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]};
      Ast.Fun {head = "FORALL";
        args =
        [(Ast.Symbol "m");
          Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]};
          Ast.Fun {head = "FORALL";
            args =
            [(Ast.Symbol "i");
              Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]};
              Ast.Fun {head = "FORALL";
                args =
                [(Ast.Symbol "i'");
                  Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]};
                  Ast.Fun {head = "FORALL";
                    args =
                    [(Ast.Symbol "x");
                      Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]};
                      Ast.Fun {head = "FORALL";
                        args =
                        [(Ast.Symbol "x'");
                          Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]};
                          Ast.Fun {head = "FORALL";
                            args =
                            [(Ast.Symbol "b");
                              Ast.Fun {head = "CVAR";
                                args = [(Ast.Symbol "BIT")]};
                              Ast.Fun {head = "FORALL";
                                args =
                                [(Ast.Symbol "b'");
                                  Ast.Fun {head = "CVAR";
                                    args = [(Ast.Symbol "BIT")]};
                                  Ast.Fun {head = "FORALL";
                                    args =
                                    [(Ast.Symbol "q");
                                      Ast.Fun {head = "QREG";
                                        args = [(Ast.Symbol "BIT")]};
                                      Ast.Fun {head = "JUDGEMENT";
                                        args =
                                        [Ast.Fun {head = "VBAR";
                                           args =
                                           [Ast.Fun {head = "IMPLY";
                                              args =
                                              [Ast.Fun {head = "NOT";
                                                 args =
                                                 [Ast.Fun {head = "EQEQ";
                                                    args =
                                                    [(Ast.Symbol "x");
                                                      (Ast.Symbol "x'")]}
                                                   ]};
                                                Ast.Fun {head = "SUBSCRIPT";
                                                  args =
                                                  [Ast.Fun {head = "ZEROO";
                                                     args =
                                                     [(Ast.Symbol "BIT");
                                                       (Ast.Symbol "BIT")]};
                                                    Ast.Fun {head = "PAIR";
                                                      args =
                                                      [(Ast.Symbol "q");
                                                        (Ast.Symbol "q")]}
                                                    ]}
                                                ]};
                                             Ast.Fun {head = "SUBSCRIPT";
                                               args =
                                               [Ast.Fun {head = "ZEROO";
                                                  args =
                                                  [(Ast.Symbol "BIT");
                                                    (Ast.Symbol "BIT")]};
                                                 Ast.Fun {head = "PAIR";
                                                   args =
                                                   [(Ast.Symbol "q");
                                                     (Ast.Symbol "q")]}
                                                 ]}
                                             ]};
                                          Ast.Fun {head = "SEQ";
                                            args =
                                            [Ast.Fun {head = "ASSIGN";
                                               args =
                                               [(Ast.Symbol "i");
                                                 (Ast.Symbol "n")]};
                                              Ast.Fun {head = "WHILE";
                                                args =
                                                [Ast.Fun {head = "APPLY";
                                                   args =
                                                   [Ast.Fun {head = "APPLY";
                                                      args =
                                                      [(Ast.Symbol "lt");
                                                        (Ast.Symbol "i")]};
                                                     (Ast.Symbol "m")]};
                                                  Ast.Fun {head = "SEQ";
                                                    args =
                                                    [Ast.Fun {
                                                       head = "PASSIGN";
                                                       args =
                                                       [(Ast.Symbol "b");
                                                         (Ast.Symbol "miu")]};
                                                      Ast.Fun {
                                                        head = "ASSIGN";
                                                        args =
                                                        [(Ast.Symbol "x");
                                                          Ast.Fun {
                                                            head = "APPLY";
                                                            args =
                                                            [Ast.Fun {
                                                               head = "APPLY";
                                                               args =
                                                               [(Ast.Symbol
                                                                   "iADD");
                                                                 (Ast.Symbol
                                                                    "x")
                                                                 ]};
                                                              (Ast.Symbol "b")
                                                              ]}
                                                          ]}
                                                      ]}
                                                  ]}
                                              ]};
                                          Ast.Fun {head = "SEQ";
                                            args =
                                            [Ast.Fun {head = "ASSIGN";
                                               args =
                                               [(Ast.Symbol "i'");
                                                 (Ast.Symbol "n")]};
                                              Ast.Fun {head = "WHILE";
                                                args =
                                                [Ast.Fun {head = "APPLY";
                                                   args =
                                                   [Ast.Fun {head = "APPLY";
                                                      args =
                                                      [(Ast.Symbol "lt");
                                                        (Ast.Symbol "i'")]};
                                                     (Ast.Symbol "m")]};
                                                  Ast.Fun {head = "SEQ";
                                                    args =
                                                    [Ast.Fun {
                                                       head = "INITQUBIT";
                                                       args =
                                                       [(Ast.Symbol "q")]};
                                                      Ast.Fun {
                                                        head = "UNITARY";
                                                        args =
                                                        [(Ast.Symbol "H");
                                                          (Ast.Symbol "q")]};
                                                      Ast.Fun {head = "MEAS";
                                                        args =
                                                        [(Ast.Symbol "b'");
                                                          Ast.Fun {
                                                            head = "PAIR";
                                                            args =
                                                            [(Ast.Symbol "P0");
                                                              (Ast.Symbol
                                                                 "P1")
                                                              ]};
                                                          (Ast.Symbol "q")]};
                                                      Ast.Fun {
                                                        head = "ASSIGN";
                                                        args =
                                                        [(Ast.Symbol "x'");
                                                          Ast.Fun {
                                                            head = "APPLY";
                                                            args =
                                                            [Ast.Fun {
                                                               head = "APPLY";
                                                               args =
                                                               [(Ast.Symbol
                                                                   "iADD");
                                                                 (Ast.Symbol
                                                                    "x'")
                                                                 ]};
                                                              (Ast.Symbol
                                                                 "b'")
                                                              ]}
                                                          ]}
                                                      ]}
                                                  ]}
                                              ]};
                                          Ast.Fun {head = "VBAR";
                                            args =
                                            [Ast.Fun {head = "IMPLY";
                                               args =
                                               [Ast.Fun {head = "NOT";
                                                  args =
                                                  [Ast.Fun {head = "EQEQ";
                                                     args =
                                                     [(Ast.Symbol "x");
                                                       (Ast.Symbol "x'")]}
                                                    ]};
                                                 Ast.Fun {head = "SUBSCRIPT";
                                                   args =
                                                   [Ast.Fun {head = "ZEROO";
                                                      args =
                                                      [(Ast.Symbol "BIT");
                                                        (Ast.Symbol "BIT")]};
                                                     Ast.Fun {head = "PAIR";
                                                       args =
                                                       [(Ast.Symbol "q");
                                                         (Ast.Symbol "q")]}
                                                     ]}
                                                 ]};
                                              Ast.Fun {head = "SUBSCRIPT";
                                                args =
                                                [Ast.Fun {head = "ZEROO";
                                                   args =
                                                   [(Ast.Symbol "BIT");
                                                     (Ast.Symbol "BIT")]};
                                                  Ast.Fun {head = "PAIR";
                                                    args =
                                                    [(Ast.Symbol "q");
                                                      (Ast.Symbol "q")]}
                                                  ]}
                                              ]}
                                          ]}
                                      ]}
                                  ]}
                              ]}
                          ]}
                      ]}
                  ]}
              ]}
          ]}
      ]};
  goals =
  [([Ast.Assumption {name = "q";
       t = Ast.Fun {head = "QREG"; args = [(Ast.Symbol "BIT")]}};
      Ast.Assumption {name = "b'";
        t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "BIT")]}};
      Ast.Assumption {name = "b";
        t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "BIT")]}};
      Ast.Assumption {name = "x'";
        t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
      Ast.Assumption {name = "x";
        t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
      Ast.Assumption {name = "i'";
        t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
      Ast.Assumption {name = "i";
        t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
      Ast.Assumption {name = "m";
        t = Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]}};
      Ast.Assumption {name = "n";
        t = Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]}}
      ],
    Ast.Fun {head = "ENTAILMENT";
      args =
      [Ast.Fun {head = "VBAR";
         args =
         [Ast.Fun {head = "IMPLY";
            args =
            [Ast.Fun {head = "NOT";
               args =
               [Ast.Fun {head = "EQEQ";
                  args = [(Ast.Symbol "x"); (Ast.Symbol "x'")]}
                 ]};
              Ast.Fun {head = "SUBSCRIPT";
                args =
                [Ast.Fun {head = "ZEROO";
                   args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                  Ast.Fun {head = "PAIR";
                    args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                  ]}
              ]};
           Ast.Fun {head = "SUBSCRIPT";
             args =
             [Ast.Fun {head = "ZEROO";
                args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
               Ast.Fun {head = "PAIR";
                 args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
               ]}
           ]};
        Ast.Fun {head = "VBAR";
          args =
          [Ast.Fun {head = "WEDGE";
             args =
             [Ast.Fun {head = "IMPLY";
                args =
                [Ast.Fun {head = "NOT";
                   args =
                   [Ast.Fun {head = "WEDGE";
                      args =
                      [Ast.Fun {head = "NOT";
                         args =
                         [Ast.Fun {head = "APPLY";
                            args =
                            [Ast.Fun {head = "APPLY";
                               args = [(Ast.Symbol "lt"); (Ast.Symbol "i")]};
                              (Ast.Symbol "m")]}
                           ]};
                        Ast.Fun {head = "NOT";
                          args =
                          [Ast.Fun {head = "APPLY";
                             args =
                             [Ast.Fun {head = "APPLY";
                                args = [(Ast.Symbol "lt"); (Ast.Symbol "i'")]};
                               (Ast.Symbol "m")]}
                            ]}
                        ]}
                     ]};
                  Ast.Fun {head = "SUBSCRIPT";
                    args =
                    [Ast.Fun {head = "ZEROO";
                       args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                      Ast.Fun {head = "PAIR";
                        args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                      ]}
                  ]};
               Ast.Fun {head = "IMPLY";
                 args =
                 [Ast.Fun {head = "NOT";
                    args =
                    [Ast.Fun {head = "WEDGE";
                       args =
                       [Ast.Fun {head = "EQEQ";
                          args = [(Ast.Symbol "x"); (Ast.Symbol "x'")]};
                         Ast.Fun {head = "EQEQ";
                           args = [(Ast.Symbol "i"); (Ast.Symbol "i'")]}
                         ]}
                      ]};
                   Ast.Fun {head = "SUBSCRIPT";
                     args =
                     [Ast.Fun {head = "ZEROO";
                        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                       Ast.Fun {head = "PAIR";
                         args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                       ]}
                   ]}
               ]};
            Ast.Fun {head = "SUBSCRIPT";
              args =
              [Ast.Fun {head = "ZEROO";
                 args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                Ast.Fun {head = "PAIR";
                  args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                ]}
            ]}
        ]});
    ([Ast.Assumption {name = "q";
        t = Ast.Fun {head = "QREG"; args = [(Ast.Symbol "BIT")]}};
       Ast.Assumption {name = "b'";
         t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "BIT")]}};
       Ast.Assumption {name = "b";
         t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "BIT")]}};
       Ast.Assumption {name = "x'";
         t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
       Ast.Assumption {name = "x";
         t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
       Ast.Assumption {name = "i'";
         t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
       Ast.Assumption {name = "i";
         t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
       Ast.Assumption {name = "m";
         t = Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]}};
       Ast.Assumption {name = "n";
         t = Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]}}
       ],
     Ast.Fun {head = "JUDGEMENT";
       args =
       [Ast.Fun {head = "VBAR";
          args =
          [Ast.Fun {head = "WEDGE";
             args =
             [Ast.Fun {head = "IMPLY";
                args =
                [Ast.Fun {head = "NOT";
                   args =
                   [Ast.Fun {head = "WEDGE";
                      args =
                      [Ast.Fun {head = "APPLY";
                         args =
                         [Ast.Fun {head = "APPLY";
                            args = [(Ast.Symbol "lt"); (Ast.Symbol "i")]};
                           (Ast.Symbol "m")]};
                        Ast.Fun {head = "APPLY";
                          args =
                          [Ast.Fun {head = "APPLY";
                             args = [(Ast.Symbol "lt"); (Ast.Symbol "i'")]};
                            (Ast.Symbol "m")]}
                        ]}
                     ]};
                  Ast.Fun {head = "SUBSCRIPT";
                    args =
                    [Ast.Fun {head = "ZEROO";
                       args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                      Ast.Fun {head = "PAIR";
                        args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                      ]}
                  ]};
               Ast.Fun {head = "IMPLY";
                 args =
                 [Ast.Fun {head = "NOT";
                    args =
                    [Ast.Fun {head = "WEDGE";
                       args =
                       [Ast.Fun {head = "EQEQ";
                          args = [(Ast.Symbol "x"); (Ast.Symbol "x'")]};
                         Ast.Fun {head = "EQEQ";
                           args = [(Ast.Symbol "i"); (Ast.Symbol "i'")]}
                         ]}
                      ]};
                   Ast.Fun {head = "SUBSCRIPT";
                     args =
                     [Ast.Fun {head = "ZEROO";
                        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                       Ast.Fun {head = "PAIR";
                         args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                       ]}
                   ]}
               ]};
            Ast.Fun {head = "SUBSCRIPT";
              args =
              [Ast.Fun {head = "ZEROO";
                 args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                Ast.Fun {head = "PAIR";
                  args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                ]}
            ]};
         Ast.Fun {head = "SEQ";
           args =
           [Ast.Fun {head = "PASSIGN";
              args = [(Ast.Symbol "b"); (Ast.Symbol "miu")]};
             Ast.Fun {head = "ASSIGN";
               args =
               [(Ast.Symbol "x");
                 Ast.Fun {head = "APPLY";
                   args =
                   [Ast.Fun {head = "APPLY";
                      args = [(Ast.Symbol "iADD"); (Ast.Symbol "x")]};
                     (Ast.Symbol "b")]}
                 ]}
             ]};
         Ast.Fun {head = "SEQ";
           args =
           [Ast.Fun {head = "INITQUBIT"; args = [(Ast.Symbol "q")]};
             Ast.Fun {head = "UNITARY";
               args = [(Ast.Symbol "H"); (Ast.Symbol "q")]};
             Ast.Fun {head = "MEAS";
               args =
               [(Ast.Symbol "b'");
                 Ast.Fun {head = "PAIR";
                   args = [(Ast.Symbol "P0"); (Ast.Symbol "P1")]};
                 (Ast.Symbol "q")]};
             Ast.Fun {head = "ASSIGN";
               args =
               [(Ast.Symbol "x'");
                 Ast.Fun {head = "APPLY";
                   args =
                   [Ast.Fun {head = "APPLY";
                      args = [(Ast.Symbol "iADD"); (Ast.Symbol "x'")]};
                     (Ast.Symbol "b'")]}
                 ]}
             ]};
         Ast.Fun {head = "VBAR";
           args =
           [Ast.Fun {head = "WEDGE";
              args =
              [Ast.Fun {head = "IMPLY";
                 args =
                 [Ast.Fun {head = "NOT";
                    args =
                    [Ast.Fun {head = "EQEQ";
                       args =
                       [Ast.Fun {head = "APPLY";
                          args =
                          [Ast.Fun {head = "APPLY";
                             args = [(Ast.Symbol "lt"); (Ast.Symbol "i")]};
                            (Ast.Symbol "m")]};
                         Ast.Fun {head = "APPLY";
                           args =
                           [Ast.Fun {head = "APPLY";
                              args = [(Ast.Symbol "lt"); (Ast.Symbol "i'")]};
                             (Ast.Symbol "m")]}
                         ]}
                      ]};
                   Ast.Fun {head = "SUBSCRIPT";
                     args =
                     [Ast.Fun {head = "ZEROO";
                        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                       Ast.Fun {head = "PAIR";
                         args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                       ]}
                   ]};
                Ast.Fun {head = "IMPLY";
                  args =
                  [Ast.Fun {head = "NOT";
                     args =
                     [Ast.Fun {head = "WEDGE";
                        args =
                        [Ast.Fun {head = "EQEQ";
                           args = [(Ast.Symbol "x"); (Ast.Symbol "x'")]};
                          Ast.Fun {head = "EQEQ";
                            args = [(Ast.Symbol "i"); (Ast.Symbol "i'")]}
                          ]}
                       ]};
                    Ast.Fun {head = "SUBSCRIPT";
                      args =
                      [Ast.Fun {head = "ZEROO";
                         args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                        Ast.Fun {head = "PAIR";
                          args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                        ]}
                    ]}
                ]};
             Ast.Fun {head = "SUBSCRIPT";
               args =
               [Ast.Fun {head = "ZEROO";
                  args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
                 Ast.Fun {head = "PAIR";
                   args = [(Ast.Symbol "q"); (Ast.Symbol "q")]}
                 ]}
             ]}
         ]})
    ];
  lean_goals =
  [([Ast.Assumption {name = "q";
       t = Ast.Fun {head = "QREG"; args = [(Ast.Symbol "BIT")]}};
      Ast.Assumption {name = "b'";
        t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "BIT")]}};
      Ast.Assumption {name = "b";
        t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "BIT")]}};
      Ast.Assumption {name = "x'";
        t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
      Ast.Assumption {name = "x";
        t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
      Ast.Assumption {name = "i'";
        t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
      Ast.Assumption {name = "i";
        t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
      Ast.Assumption {name = "m";
        t = Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]}};
      Ast.Assumption {name = "n";
        t = Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]}}
      ],
    Ast.Fun {head = "EQ";
      args =
      [
        Ast.Fun {head = "IMPLY";
         args =
         [Ast.Fun {head = "WEDGE";
            args =
            [Ast.Fun {head = "EQEQ";
               args = [(Ast.Symbol "x"); (Ast.Symbol "x'")]};
              Ast.Fun {head = "EQEQ";
                args = [(Ast.Symbol "i"); (Ast.Symbol "i'")]}
              ]};
           Ast.Fun {head = "WEDGE";
             args =
             [Ast.Fun {head = "EQEQ";
                args =
                [Ast.Fun {head = "APPLY";
                   args =
                   [Ast.Fun {head = "APPLY";
                      args = [(Ast.Symbol "lt"); (Ast.Symbol "i")]};
                     (Ast.Symbol "m")]};
                  Ast.Fun {head = "APPLY";
                    args =
                    [Ast.Fun {head = "APPLY";
                       args = [(Ast.Symbol "lt"); (Ast.Symbol "i'")]};
                      (Ast.Symbol "m")]}
                  ]};
               Ast.Fun {head = "WEDGE";
                 args =
                 [Ast.Fun {head = "EQEQ";
                    args = [(Ast.Symbol "x"); (Ast.Symbol "x'")]};
                   Ast.Fun {head = "EQEQ";
                     args = [(Ast.Symbol "i"); (Ast.Symbol "i'")]}
                   ]}
               ]}
           ]};
        (Ast.Symbol "true")]})
    ]
  }