%%
% Copyright 2017 Harm Brouwer <me@hbrouwer.eu>
%                Noortje Venhuizen <njvenhuizen@gmail.com>
%
% Licensed under the Apache License, Version 2.0 (the "License");
% you may not use this file except in compliance with the License.
% You may obtain a copy of the License at
%
%     http://www.apache.org/licenses/LICENSE-2.0
%
% Unless required by applicable law or agreed to in writing, software
% distributed under the License is distributed on an "AS IS" BASIS,
% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
% See the License for the specific language governing permissions and
% limitations under the License.
%%

:- module(dfs_sampling,
        [
                dfs_sample_models/2,
                dfs_sample_model/1
        ]).

:- use_module(dfs_interpretation).

% dfs_sample_models(+NumModels,-ModelSet)

dfs_sample_models(N,MS) :-
        dfs_sample_models_(N,0,MS).

dfs_sample_models_(N,N,[]) :- !.
dfs_sample_models_(N,I,[M|MS]) :-
        I0 is I + 1,
        dfs_sample_model(M),
        dfs_pprint_model(M),
        dfs_sample_models_(N,I0,MS).

% dfs_sample_model(-Model)

dfs_sample_model((Um,Vm)) :-
        constants_and_universe(Consts,Um),
        dfs_init_g((Um,_),G),
        dfs_vector_space:ifunc_inst_constants(Consts,Um,VmCs),
        dfs_constant_instantiations((_,VmCs),CIs),
        findall(P,user:property(P),Ps),
        %findall(C,user:constraint(C),Cs1),
        findall(C,(user:constraint(C0),optimize_q_forall(C0,C)),Cs1),
        flatten(Cs1,Cs),
        dfs_sample_properties(Ps,Um,G,CIs,Cs,VmCs,Vm).

% constants_and_universe(-Constants,-Entities)

constants_and_universe(Cs,Um) :-
        findall(C,user:constant(C),Cs),
        length(Cs,N),
        dfs_entities(N,Um).

%% dfs_sample_properties(+Properties,+Universe,+G,+ConstantInstantiatons,
%      +Constraints,+IFuncConstants,-IFunc)
%
%  Samples property instantiations using a non-deterministic, probabilistic
%  and incremental inference-driven sampling algorithm. 
%
%  The aim is to arrive at an interpretation function that satisfies a set 
%  of imposed probabilistic and hard constraints. To this end, we start out
%  with with an empty interpretation function, to which we will incrementally
%  add properties. We call this interpretation function the Light World (LVm),
%  and this function will contain all properties that are true in the model.
%  In parallel to the Light World, we will also construct a Dark World (DVm)
%  function that will contain all properties that are false in the model. 
%
%  Given LVm and DVm, a set of randomly ordered properties P, and a set of 
%  constraints C, we then do the following for each property p:
%
%  (1) Add p to LVm, yielding LVm';
%
%  (2) LT = true iff for each constraint c:
%       
%       -- c is satisfied by LVm';
%       -- or if the complement of c is not satisfied by DVm.
%
%  (3) Add p to DVm, yielding DVm';
% 
%  (4) DT = true iff for each constraint c:
%       
%       -- c is satisfied by LVm;
%       -- or if the complement of c is not satisfied by DVm'.
%   
%  (5) Depending on the outcome of (2) and (4):
%
%       -- LT & DT: Infer p with Pr(p): LVm = LVm', otherwise: DVm = DVm'
%       -- LT & !DT: Infer p to be true in the Light World: LVm = LVm'
%       -- !LT & DT: Infer p to be true in the Dark World: DVm = DVm'
%       -- !LT & !DT: The model is inconsistent, and needs to be discarded.
%
%  (6) Repeat (1) for next p. If each p is a property in either LVm or DVm,
%      and LVm satisfies all constraints, LVm is the final interpretation 
%      function.

dfs_sample_properties(Ps,Um,G,CIs,Cs,VmCs,Vm) :-
        random_permutation(Ps,Ps1),
        dfs_sample_properties_(Ps1,Um,G,CIs,Cs,VmCs,VmCs,Vm), !.
dfs_sample_properties(Ps,Um,G,CIs,Cs,VmCs,Vm) :-
        write('Retry!\n'),
        dfs_sample_properties(Ps,Um,G,CIs,Cs,VmCs,Vm).

dfs_sample_properties_([],Um,G,_,Cs,Vm,_,Vm) :- 
        dfs_interpret(Cs,(Um,Vm),G).
dfs_sample_properties_([P|Ps],Um,G,CIs,Cs,LVm0,DVm0,LVm) :-
        P =.. [Prop|Args],
        dfs_terms_to_entities(Args,CIs,Es),
        add_property(LVm0,Prop,Es,LVm1),
        ( satisfies_constraints(Cs,(Um,LVm1),(Um,DVm0),G) -> LT = 1 ; LT = 0 ),     %% light world
        add_property(DVm0,Prop,Es,DVm1),
        ( satisfies_constraints(Cs,(Um,LVm0),(Um,DVm1),G) -> DT = 1 ; DT = 0 ),     %% dark world
        (  LT == 1, DT == 1             %% undecided
        -> (  probabilistic_choice(P,(Um,LVm0),G)
           -> dfs_sample_properties_(Ps,Um,G,CIs,Cs,LVm1,DVm0,LVm)
           ;  dfs_sample_properties_(Ps,Um,G,CIs,Cs,LVm0,DVm1,LVm) )
        ;  (  LT == 1, DT == 0          %% light world
           -> dfs_sample_properties_(Ps,Um,G,CIs,Cs,LVm1,DVm0,LVm)
           ;  (  LT == 0, DT == 1       %% dark world
              -> dfs_sample_properties_(Ps,Um,G,CIs,Cs,LVm0,DVm1,LVm)
              ;  false ) ) ).           %% inconsistent

%% add_property(+IFunc,+Property,+Entities,-IFunc)
%
%  Adds a property for a set of entities to an interpretation function.

add_property([],Prop,[E|Es],[P1]) :-
        (  Es == []
        -> P1 =.. [Prop|[[E]]]          %% unary predicates
        ;  P1 =.. [Prop|[[[E|Es]]]] ).  %% n-ary predicates
add_property([P0|P0s],Prop,[E|Es],[P1|P0s]) :-
        P0 =.. [Prop|_], !,
        (  Es == []
        -> P0 =.. [Prop|[Es0]],         %% unary predicates
           P1 =.. [Prop|[[E|Es0]]]      
        ;  P0 =.. [Prop|[Es0]],         %% n-ary predicates
           P1 =.. [Prop|[[[E|Es]|Es0]]] ).
add_property([P0|P0s],Prop,Es,[P0|P1s]) :-
        add_property(P0s,Prop,Es,P1s).

%% satisfies_constraints(+Constraints,+LightModel,+DarkModel,+G)
%
%  Returns true when each constraint is either satisfied in the light world,
%  or when its complement is not satisfied in the dark world.

satisfies_constraints([],_,_,_).
satisfies_constraints([C|Cs],LM,DM,G) :-
        dfs_interpret(C,LM,G), !,
        satisfies_constraints(Cs,LM,DM,G).
satisfies_constraints([C|Cs],LM,DM,G) :-
        complement(C,Cc),
        \+ dfs_interpret(Cc,DM,G),
        satisfies_constraints(Cs,LM,DM,G).

%% complement(?Formula,?ComplementFormula)
%
%  Complement of truth/falsehood conditions.

complement(neg(P0),neg(P1)) :-
        !, % !P => !P
        complement(P0,P1).
complement(and(P0,Q0),or(P1,Q1)) :-
        !, % P & Q => P | Q
        complement(P0,P1),
        complement(Q0,Q1).
complement(or(P0,Q0),and(P1,Q1)) :-
        !, % P | Q => P & Q
        complement(P0,P1),
        complement(Q0,Q1).
complement(xor(P0,Q0),or(and(P1,Q1),and(neg(P1),neg(Q1)))) :-
        !, % P (+) Q => (P & Q) | (!P & !Q)
        complement(P0,P1),
        complement(Q0,Q1). 
complement(imp(P0,Q0),and(neg(P1),Q1)) :-
        !, % P -> Q => !P & Q
        complement(P0,P1),
        complement(Q0,Q1).
complement(iff(P0,Q0),or(and(neg(P1),Q1),and(P1,neq(Q1)))) :-
        !, % P <-> Q => (!P & Q) | (P & !Q)
        complement(P0,P1),
        complement(Q0,Q1).
complement(exists(X,P0),forall(X,P1)) :-
        !, % ∃x P => ∀x P
        complement(P0,P1).
complement(forall(X,P0),exists(X,P1)) :-
        !, % ∀x P => ∃x P
        complement(P0,P1).
complement(P,P).

%% probabilistic_choice(?Formula,+Model,+G)
%
%  Returns a probabilistically determined truth value for Formula, given
%  a Model (thus far) and assignment function G.

probabilistic_choice(P,M,G) :-
        user:probability(P,C,Pr),
        dfs_interpret(C,M,G), 
        maybe(Pr).
        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% forall optimization %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

optimize_q_forall(P,FIs) :-
        vis(P,[],[],VIs),
        findall(FI,fi(P,VIs,FI),FIs).

fi(neg(P0),     VIs,neg(P1)     ) :- !, fi(P0,VIs,P1).
fi(and(P0,Q0),  VIs,and(P1,Q1)  ) :- !, fi(P0,VIs,P1), fi(Q0,VIs,Q1).
fi(or(P0,Q0),   VIs,or(P1,Q1)   ) :- !, fi(P0,VIs,P1), fi(Q0,VIs,Q1).
fi(xor(P0,Q0),  VIs,xor(P1,Q1)  ) :- !, fi(P0,VIs,P1), fi(Q0,VIs,Q1).
fi(imp(P0,Q0),  VIs,imp(P1,Q1)  ) :- !, fi(P0,VIs,P1), fi(Q0,VIs,Q1).
fi(iff(P0,Q0),  VIs,iff(P1,Q1)  ) :- !, fi(P0,VIs,P1), fi(Q0,VIs,Q1).
fi(exists(X,P0),VIs,exists(X,P1)) :- !, fi(P0,VIs,P1).
fi(forall(X,P0),VIs,P1) :-
        q_imp_chain(X,forall(X,P0)), !,
        select_vi(X,VIs,VIs0),
        fi(P0,VIs0,P1).
fi(forall(X,P0),VIs,forall(X,P1)) :- !, fi(P0,VIs,P1).
fi(top,_,top) :- !.
fi(bottom,_,bottom) :- !.
fi(P0,VIs,P1) :-
        prop_instance(P0,VIs,P1).

select_vi(V,VIs,[V=X|VIs1]) :-
        findall(V=X,member(V=X,VIs),VIs0),
        findall(V1=Y,(member(V1=Y,VIs),V1\=V),VIs1),
        select(V=X,VIs0,_).

prop_instance(P,VIs,PI) :-
        P =.. [Prop|As],
        prop_instance_(As,VIs,AIs),
        PI =.. [Prop|AIs].

prop_instance_([],_,[]).
prop_instance_([A|As],VIs,[E|IAs]) :-
        memberchk(A=E,VIs), !,
        prop_instance_(As,VIs,IAs).
prop_instance_([A|As],VIs,[A|IAs]) :-
        prop_instance_(As,VIs,IAs).

vis(neg(P),     Vs,VIs0,VIs1) :- !, vis(P,Vs,VIs0,VIs1).
vis(and(P,Q),   Vs,VIs0,VIs2) :- !, vis(P,Vs,VIs0,VIs1), vis(Q,Vs,VIs1,VIs2).
vis(or(P,Q),    Vs,VIs0,VIs2) :- !, vis(P,Vs,VIs0,VIs1), vis(Q,Vs,VIs1,VIs2).
vis(xor(P,Q),   Vs,VIs0,VIs2) :- !, vis(P,Vs,VIs0,VIs1), vis(Q,Vs,VIs1,VIs2).
vis(imp(P,Q),   Vs,VIs0,VIs2) :- !, vis(P,Vs,VIs0,VIs1), vis(Q,Vs,VIs1,VIs2).
vis(iff(P,Q),   Vs,VIs0,VIs2) :- !, vis(P,Vs,VIs0,VIs1), vis(Q,Vs,VIs1,VIs2).
vis(exists(_,P),Vs,VIs0,VIs1) :- !, vis(P,Vs,VIs0,VIs1).
vis(forall(X,P),Vs,VIs0,VIs2) :-
        !,
        (  q_imp_chain(X,forall(X,P))
        -> vis(P,[X|Vs],VIs0,VIs1)
        ;  vis(P,Vs,VIs0,VIs1) ),
        vis(P,Vs,VIs1,VIs2).
vis(top,_,VIs0,VIs0) :- !.
vis(bottom,_,VIs0,VIs0) :- !.
vis(P,Vs,VIs0,VIs1) :- 
        vis_(P,Vs,VIs0,VIs1).

vis_(_,[],VIs,VIs) :- !.
vis_(P,[V|Vs],VIs0,VIs4) :-
        prop_template(P,V,Templ,X), !,
        findall(V=X,user:property(Templ),VIs1),
        list_to_ord_set(VIs1,VIs2),
        union(VIs0,VIs2,VIs3),
        vis_(P,Vs,VIs3,VIs4).
vis_(P,[_|Vs],VIsAcc,VIs) :-
        vis_(P,Vs,VIsAcc,VIs).

q_imp_chain(X,forall(_,imp(P,_))) :- 
        vis(P,[X],[],VIs),
        memberchk(X=_,VIs).
q_imp_chain(X,forall(_,P)) :-
        q_imp_chain(X,P).

prop_template(P,V,Templ,X) :-
        P =.. [Prop|As],
        memberchk(V,As),
        prop_template_(As,V,TAs,X),
        Templ =.. [Prop|TAs].

prop_template_([],_,[],_).
prop_template_([V|As],V,[X|TAs],X) :-
        !, prop_template_(As,V,TAs,X).
prop_template_([_|As],V,[_|TAs],X) :-
        prop_template_(As,V,TAs,X).

% %%%%%%%%%%%%%%%
% %%%% debug %%%%
% %%%%%%%%%%%%%%%

% valid_instance(P) :-
%         P =.. [(=)|_], !.
% valid_instance(P) :-
%         P =.. [_|As],
%         dfs_variables(Vs),
%         valid_instance_(P,As,Vs).

% valid_instance_(_,[],_) :- !.
% valid_instance_(P,[A|As],Vs) :-
%         memberchk(A,Vs), !,
%         valid_instance_(P,As,Vs).
% valid_instance_(P,[A|As],Vs) :-
%         prop_template(P,A,Templ,A),
%         user:property(Templ), !,
%         valid_instance_(P,As,Vs).

% %%%%%%%%%%%%%%%
% %%%%%%%%%%%%%%%

dbg_constraints :-
        findall(C,constraint(C),Cs),
        dbg_constraints_(Cs,org).

dbg_constraints_([],_).
dbg_constraints_([C|Cs],org) :-
        !, complement(C,Cc),
        format('\nC: ~w => ~w\n',[C,Cc]),
        optimize_q_forall(C,OCs),
        dbg_constraints_(OCs,opt),
        dbg_constraints_(Cs,org).
dbg_constraints_([OC|OCs],opt) :-
        complement(OC,OCc),
        format('O: ~w ==> ~w\n',[OC,OCc]),
        dbg_constraints_(OCs,opt).

% dbg_validate([],_,_).
% dbg_validate([C|Cs],M,G) :-
%         dfs_interpret(C,M,G), !,
%         dbg_validate(Cs,M,G).
% dbg_validate([C|_],_,_) :-
%         nl, write(C), nl,
%         complement(C,Cc),
%         write(Cc), nl, nl,
%         false.

% dfs_sample_properties_([],Um,G,_,Cs,Vm,_,Vm) :-
%         dbg_validate(Cs,(Um,Vm),G), !.
%         %dfs_interpret(Cs,(Um,Vm),G), !.
% dfs_sample_properties_([P|Ps],Um,G,CIs,Cs,LVm0,DVm0,LVm) :-
%         P =.. [Prop|Args],
%         dfs_terms_to_entities(Args,CIs,Es),
%         add_property(LVm0,Prop,Es,LVm1),
%         ( satisfies_constraints(Cs,(Um,LVm1),(Um,DVm0),G) -> LT = 1 ; LT = 0 ),     %% light world
%         add_property(DVm0,Prop,Es,DVm1),
%         ( satisfies_constraints(Cs,(Um,LVm0),(Um,DVm1),G) -> DT = 1 ; DT = 0 ),     %% dark world
%         format('Prop: ~w\t\t\t', P),
%         %format('LVm1: ~w\n', (Um,LVm1)),
%         %format('DVm0: ~w\n', (Um,DVm0)),
%         format('LT  : ~d\t', LT),
%         %format('LVm0: ~w\n', (Um,LVm0)),
%         %format('DVm1: ~w\n', (Um,DVm1)),
%         format('DT  : ~d\t', DT),
%         (  LT == 1, DT == 1             %% undecided
%         -> (  probabilistic_choice(P,(Um,LVm0),G)
%            -> format('==> Flip to Light\n'),
%               dfs_sample_properties_(Ps,Um,G,CIs,Cs,LVm1,DVm0,LVm)
%            ;  format('==> Flip to Dark\n'),
%               dfs_sample_properties_(Ps,Um,G,CIs,Cs,LVm0,DVm1,LVm) )
%         ;  (  LT == 1, DT == 0          %% light world
%            -> format('==> Infer to Light\n'),
%               dfs_sample_properties_(Ps,Um,G,CIs,Cs,LVm1,DVm0,LVm)
%            ;  (  LT == 0, DT == 1       %% dark world
%               -> format('==> Infer to Dark\n'),
%                  dfs_sample_properties_(Ps,Um,G,CIs,Cs,LVm0,DVm1,LVm)
%               ;  format('==> Restart ...\n\n\n'),
%                  false ) ) ).           %% inconsistent
