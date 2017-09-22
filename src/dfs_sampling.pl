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
                dfs_sample_model/1,
                dfs_sample_models/2
        ]).

:- use_module(dfs_interpretation).

dfs_sample_model((Um,Vm1)) :-
        constants_and_universe(Cs,Um),
        dfs_vector_space:ifunc_inst_constants(Cs,Um,Vm0),
        dfs_constant_instantiations((_,Vm0),CIs),
        findall(P,property(P),Ps),
        dfs_init_g((Um,_),G),
        dfs_sample_properties(Ps,Um,G,CIs,Vm0,Vm1).

dfs_sample_models(N,MS) :-
        dfs_sample_models_(N,0,MS).

dfs_sample_models_(N,N,[]) :- !.
dfs_sample_models_(N,I,[M|MS]) :-
        I0 is I + 1,
        dfs_sample_model(M),
        dfs_pprint_model(M),
        dfs_sample_models_(N,I0,MS).

constants_and_universe(Cs,Um) :-
        findall(C,user:constant(C),Cs),
        length(Cs,N),
        dfs_entities(N,Um).

dfs_sample_properties(Ps,Um,G,CIs,Vm0,Vm1) :-
        findall(C,user:constraint(C),Cs),
        dfs_interpretation:conjoin(Cs,LCs),
        negate_and_simplify(Cs,Cs1),
        dfs_interpretation:conjoin(Cs1,DCs),
        %write(LCs), nl,
        %write(DCs), nl,
        dfs_sample_properties_(Ps,Um,G,CIs,LCs,Vm0,DCs,Vm0,Vm1).
        
negate_and_simplify([],[]) :- !.
negate_and_simplify([C0|Cs0],[C1|Cs1]) :-
        simplify_formula(neg(C0),C1),
        negate_and_simplify(Cs0,Cs1).

simplify_formula(neg(neg(P0)),P1) :-
        !, simplify_formula(P0,P1).
simplify_formula(neg(forall(X,P0)),exists(X,P1)) :-
        !, simplify_formula(neg(P0),P1).
simplify_formula(neg(imp(P0,Q0)),and(P1,Q1)) :-
        !, simplify_formula(P0,P1),
        simplify_formula(neg(Q0),Q1).
% simplify_formula(forall(X,imp(P0,Q0)),imp(exists(X,P1),forall(X,imp(P1,Q1)))) :-
%         !, simplify_formula(P0,P1),
%         simplify_formula(Q0,Q1).
% simplify_formula(forall(X,forall(Y,imp(P0,Q0))),imp(exists(X,exists(Y,P1)),forall(X,forall(Y,imp(P1,Q1))))) :-
%         !, simplify_formula(P0,P1),
%         simplify_formula(Q0,Q1).
simplify_formula(P,P).

dfs_sample_properties_([],_,_,_,_,Vm,_,_,Vm) :- !.
dfs_sample_properties_([P|Ps],Um,G,CIs,LCs,LVm0,DCs,DVm0,LVm3) :-
        P =.. [Prop|Args],
        dfs_terms_to_entities(Args,CIs,Es),
        add_property(LVm0,Prop,Es,LVm1),
        add_property(DVm0,Prop,Es,DVm1),
        ( satisfies_constraints(LCs,(Um,LVm1),DCs,(Um,DVm0),G) -> S1 = 1 ; S1 = 0 ),     %% light world
        ( satisfies_constraints(LCs,(Um,LVm0),DCs,(Um,DVm1),G) -> S0 = 1 ; S0 = 0 ),     %% dark world
        (  S0 == 1, S1 == 1             %% undecided
        -> probability(P,LVm0,Pr),
           (  maybe(Pr)
           -> dfs_sample_properties_(Ps,Um,G,CIs,LCs,LVm1,DCs,DVm0,LVm3)
           ;  dfs_sample_properties_(Ps,Um,G,CIs,LCs,LVm0,DCs,DVm1,LVm3)
           )
        ;  (  S0 == 0, S1 == 1          %% light world
           -> dfs_sample_properties_(Ps,Um,G,CIs,LCs,LVm1,DCs,DVm0,LVm3)
           ;  (  S0 == 1, S1 == 0       %% dark world
              -> dfs_sample_properties_(Ps,Um,G,CIs,LCs,LVm0,DCs,DVm1,LVm3)
              ;  false                  %% XXX: ?? inconsistent ??
              )                
           )
        ).

satisfies_constraints(LCs,LM,_,_,G) :-  %% light world
        dfs_interpret(LCs,LM,G), !.%, write('Light!\n').
satisfies_constraints(_,_,DCs,DM,G) :-  %% dark world
        dfs_interpret(DCs,DM,G), !.%, write('Dark!\n').

add_property([],Prop,[E|Es],[P1]) :-
        !,
        (  Es == []
        -> P1 =.. [Prop|[[E]]]          %% unary predicates
        ;  P1 =.. [Prop|[[[E|Es]]]] ).  %% n-ary predicates
add_property([P0|P0s],Prop,[E|Es],[P1|P0s]) :-
        P0 =.. [Prop|_], !,
        (  Es == []
        -> P0 =.. [Prop|Es0],           %% unary predicates
           P1 =.. [Prop|[[E]|Es0]]      
        ;  P0 =.. [Prop|[Es0]],         %% n-ary predicates
           P1 =.. [Prop|[[[E|Es]|Es0]]] ).
add_property([P0|P0s],Prop,Es,[P0|P1s]) :-
        add_property(P0s,Prop,Es,P1s).
