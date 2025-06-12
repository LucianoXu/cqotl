let obligation1 = 
  { Ast.env =
  [Ast.Assumption {name = "lt";
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
         ]}}
    ];
  context =
  [Ast.Assumption {name = "x'";
     t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
    Ast.Assumption {name = "x";
      t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
    Ast.Assumption {name = "i'";
      t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
    Ast.Assumption {name = "i";
      t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
    Ast.Assumption {name = "m";
      t = Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]}}
    ];
  goal =
  Ast.Fun {head = "EQ";
    args =
    [Ast.Fun {head = "IMPLY";
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
      (Ast.Symbol "true")]}
  }

let obligation2 = { Ast.env =
  [Ast.Assumption {name = "lt";
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
         ]}}
    ];
  context =
  [Ast.Assumption {name = "x'";
     t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
    Ast.Assumption {name = "x";
      t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
    Ast.Assumption {name = "i'";
      t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
    Ast.Assumption {name = "i";
      t = Ast.Fun {head = "CVAR"; args = [(Ast.Symbol "INT")]}};
    Ast.Assumption {name = "m";
      t = Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]}}
    ];
  goal =
  Ast.Fun {head = "EQ";
    args =
    [Ast.Fun {head = "IMPLY";
       args =
       [Ast.Fun {head = "WEDGE";
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
               ]};
            Ast.Fun {head = "WEDGE";
              args =
              [Ast.Fun {head = "EQEQ";
                 args = [(Ast.Symbol "x"); (Ast.Symbol "x'")]};
                Ast.Fun {head = "EQEQ";
                  args = [(Ast.Symbol "i"); (Ast.Symbol "i'")]}
                ]}
            ]};
         Ast.Fun {head = "EQEQ"; args = [(Ast.Symbol "x"); (Ast.Symbol "x'")]}
         ]};
      (Ast.Symbol "true")]}
  }

let obligation3 = { Ast.env =
  [Ast.Assumption {name = "vplus";
     t = Ast.Fun {head = "KTYPE"; args = [(Ast.Symbol "BIT")]}};
    Ast.Assumption {name = "H";
      t =
      Ast.Fun {head = "OTYPE";
        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]}}
    ];
  context = [];
  goal =
  Ast.Fun {head = "ENTAILMENT";
    args =
    [Ast.Fun {head = "APPLY";
       args =
       [Ast.Fun {head = "KET"; args = [(Ast.Symbol "false")]};
         Ast.Fun {head = "BRA"; args = [(Ast.Symbol "false")]}]};
      Ast.Fun {head = "APPLY";
        args =
        [Ast.Fun {head = "APPLY";
           args =
           [Ast.Fun {head = "ADJ"; args = [(Ast.Symbol "H")]};
             Ast.Fun {head = "APPLY";
               args =
               [(Ast.Symbol "vplus");
                 Ast.Fun {head = "ADJ"; args = [(Ast.Symbol "vplus")]}]}
             ]};
          (Ast.Symbol "H")]}
      ]}
  }

let obligation4 = 
  { Ast.env =
  [Ast.Assumption {name = "miu";
     t = Ast.Fun {head = "PDIST"; args = [(Ast.Symbol "BIT")]}};
    Ast.Definition {name = "P0";
      t =
      Ast.Fun {head = "OTYPE";
        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
      e =
      Ast.Fun {head = "APPLY";
        args =
        [Ast.Fun {head = "KET"; args = [(Ast.Symbol "false")]};
          Ast.Fun {head = "BRA"; args = [(Ast.Symbol "false")]}]}}
    ];
  context = [];
  goal =
  Ast.Fun {head = "FORALL";
    args =
    [(Ast.Symbol "rho");
      Ast.Fun {head = "OTYPE";
        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
      Ast.Fun {head = "FORALL";
        args =
        [(Ast.Symbol "pfspace");
          Ast.Fun {head = "INSPACE";
            args =
            [(Ast.Symbol "rho");
              Ast.Fun {head = "ZEROO";
                args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]}
              ]};
          Ast.Fun {head = "EQ";
            args =
            [Ast.Fun {head = "tr";
               args =
               [Ast.Fun {head = "APPLY";
                  args = [(Ast.Symbol "P0"); (Ast.Symbol "rho")]}
                 ]};
              Ast.Fun {head = "APPLY";
                args = [(Ast.Symbol "miu"); (Ast.Symbol "false")]}
              ]}
          ]}
      ]}
  }

let obligation5 = { Ast.env =
  [Ast.Assumption {name = "miu";
     t = Ast.Fun {head = "PDIST"; args = [(Ast.Symbol "BIT")]}};
    Ast.Definition {name = "P1";
      t =
      Ast.Fun {head = "OTYPE";
        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
      e =
      Ast.Fun {head = "APPLY";
        args =
        [Ast.Fun {head = "KET"; args = [(Ast.Symbol "true")]};
          Ast.Fun {head = "BRA"; args = [(Ast.Symbol "true")]}]}}
    ];
  context = [];
  goal =
  Ast.Fun {head = "FORALL";
    args =
    [(Ast.Symbol "rho");
      Ast.Fun {head = "OTYPE";
        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
      Ast.Fun {head = "FORALL";
        args =
        [(Ast.Symbol "pfspace");
          Ast.Fun {head = "INSPACE";
            args =
            [(Ast.Symbol "rho");
              Ast.Fun {head = "ZEROO";
                args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]}
              ]};
          Ast.Fun {head = "EQ";
            args =
            [Ast.Fun {head = "tr";
               args =
               [Ast.Fun {head = "APPLY";
                  args = [(Ast.Symbol "P1"); (Ast.Symbol "rho")]}
                 ]};
              Ast.Fun {head = "APPLY";
                args = [(Ast.Symbol "miu"); (Ast.Symbol "true")]}
              ]}
          ]}
      ]}
  }

let obligation6 = { Ast.env =
  [Ast.Assumption {name = "miu";
     t = Ast.Fun {head = "PDIST"; args = [(Ast.Symbol "BIT")]}};
    Ast.Definition {name = "P0";
      t =
      Ast.Fun {head = "OTYPE";
        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
      e =
      Ast.Fun {head = "APPLY";
        args =
        [Ast.Fun {head = "KET"; args = [(Ast.Symbol "false")]};
          Ast.Fun {head = "BRA"; args = [(Ast.Symbol "false")]}]}};
    Ast.Assumption {name = "vplus";
      t = Ast.Fun {head = "KTYPE"; args = [(Ast.Symbol "BIT")]}}
    ];
  context = [];
  goal =
  Ast.Fun {head = "FORALL";
    args =
    [(Ast.Symbol "rho");
      Ast.Fun {head = "OTYPE";
        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
      Ast.Fun {head = "FORALL";
        args =
        [(Ast.Symbol "pfspace");
          Ast.Fun {head = "INSPACE";
            args =
            [(Ast.Symbol "rho");
              Ast.Fun {head = "APPLY";
                args =
                [(Ast.Symbol "vplus");
                  Ast.Fun {head = "ADJ"; args = [(Ast.Symbol "vplus")]}]}
              ]};
          Ast.Fun {head = "EQ";
            args =
            [Ast.Fun {head = "tr";
               args =
               [Ast.Fun {head = "APPLY";
                  args = [(Ast.Symbol "P0"); (Ast.Symbol "rho")]}
                 ]};
              Ast.Fun {head = "APPLY";
                args = [(Ast.Symbol "miu"); (Ast.Symbol "false")]}
              ]}
          ]}
      ]}
  }

let obligation7 = { Ast.env =
  [Ast.Assumption {name = "miu";
     t = Ast.Fun {head = "PDIST"; args = [(Ast.Symbol "BIT")]}};
    Ast.Definition {name = "P1";
      t =
      Ast.Fun {head = "OTYPE";
        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
      e =
      Ast.Fun {head = "APPLY";
        args =
        [Ast.Fun {head = "KET"; args = [(Ast.Symbol "true")]};
          Ast.Fun {head = "BRA"; args = [(Ast.Symbol "true")]}]}};
    Ast.Assumption {name = "vplus";
      t = Ast.Fun {head = "KTYPE"; args = [(Ast.Symbol "BIT")]}}
    ];
  context = [];
  goal =
  Ast.Fun {head = "FORALL";
    args =
    [(Ast.Symbol "rho");
      Ast.Fun {head = "OTYPE";
        args = [(Ast.Symbol "BIT"); (Ast.Symbol "BIT")]};
      Ast.Fun {head = "FORALL";
        args =
        [(Ast.Symbol "pfspace");
          Ast.Fun {head = "INSPACE";
            args =
            [(Ast.Symbol "rho");
              Ast.Fun {head = "APPLY";
                args =
                [(Ast.Symbol "vplus");
                  Ast.Fun {head = "ADJ"; args = [(Ast.Symbol "vplus")]}]}
              ]};
          Ast.Fun {head = "EQ";
            args =
            [Ast.Fun {head = "tr";
               args =
               [Ast.Fun {head = "APPLY";
                  args = [(Ast.Symbol "P1"); (Ast.Symbol "rho")]}
                 ]};
              Ast.Fun {head = "APPLY";
                args = [(Ast.Symbol "miu"); (Ast.Symbol "true")]}
              ]}
          ]}
      ]}
  }

let obligation8 = { Ast.env =
  [Ast.Assumption {name = "lt";
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
         ]}}
    ];
  context =
  [Ast.Assumption {name = "b'";
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
      t = Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]}}
    ];
  goal =
  Ast.Fun {head = "EQ";
    args =
    [Ast.Fun {head = "NOT";
       args =
       [Ast.Fun {head = "WEDGE";
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
               ]};
            Ast.Fun {head = "WEDGE";
              args =
              [Ast.Fun {head = "WEDGE";
                 args =
                 [Ast.Fun {head = "EQEQ";
                    args = [(Ast.Symbol "x"); (Ast.Symbol "x'")]};
                   Ast.Fun {head = "EQEQ";
                     args = [(Ast.Symbol "i"); (Ast.Symbol "i'")]}
                   ]};
                Ast.Fun {head = "EQEQ";
                  args = [(Ast.Symbol "b"); (Ast.Symbol "b'")]}
                ]}
            ]}
         ]};
      (Ast.Symbol "true")]}
  }

let obligation9 = { Ast.env =
  [Ast.Assumption {name = "iADD";
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
          ]}}
    ];
  context =
  [Ast.Assumption {name = "b'";
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
      t = Ast.Fun {head = "CTERM"; args = [(Ast.Symbol "INT")]}}
    ];
  goal =
  Ast.Fun {head = "EQ";
    args =
    [Ast.Fun {head = "IMPLY";
       args =
       [Ast.Fun {head = "WEDGE";
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
               ]};
            Ast.Fun {head = "WEDGE";
              args =
              [Ast.Fun {head = "WEDGE";
                 args =
                 [Ast.Fun {head = "WEDGE";
                    args =
                    [Ast.Fun {head = "EQEQ";
                       args = [(Ast.Symbol "x"); (Ast.Symbol "x'")]};
                      Ast.Fun {head = "EQEQ";
                        args = [(Ast.Symbol "i"); (Ast.Symbol "i'")]}
                      ]};
                   Ast.Fun {head = "EQEQ";
                     args = [(Ast.Symbol "b"); (Ast.Symbol "b'")]}
                   ]};
                Ast.Fun {head = "EQEQ";
                  args =
                  [Ast.Fun {head = "APPLY";
                     args =
                     [Ast.Fun {head = "APPLY";
                        args = [(Ast.Symbol "iADD"); (Ast.Symbol "x")]};
                       (Ast.Symbol "b")]};
                    Ast.Fun {head = "APPLY";
                      args =
                      [Ast.Fun {head = "APPLY";
                         args = [(Ast.Symbol "iADD"); (Ast.Symbol "x'")]};
                        (Ast.Symbol "b'")]}
                    ]}
                ]}
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
                  args =
                  [Ast.Fun {head = "APPLY";
                     args =
                     [Ast.Fun {head = "APPLY";
                        args = [(Ast.Symbol "iADD"); (Ast.Symbol "x")]};
                       (Ast.Symbol "b")]};
                    Ast.Fun {head = "APPLY";
                      args =
                      [Ast.Fun {head = "APPLY";
                         args = [(Ast.Symbol "iADD"); (Ast.Symbol "x'")]};
                        (Ast.Symbol "b'")]}
                    ]};
                 Ast.Fun {head = "EQEQ";
                   args = [(Ast.Symbol "i"); (Ast.Symbol "i'")]}
                 ]}
             ]}
         ]};
      (Ast.Symbol "true")]}
  }