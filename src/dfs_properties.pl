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

:- module(dfs_properties,
        [
                dfs_validity/2,
                dfs_satisfiability/2,
                dfs_entailment/3,
                dfs_logical_equivalence/3
        ]).

:- use_module(dfs_interpretation).
:- use_module(dfs_vector_space).

%% dfs_validity(+Formula,+ModelSet|+ModelMatrix)
%
%  A formula P is valid (|= P) iff:
% 
%       P is true (not false) in all models

dfs_validity(_,[]) :- !.
dfs_validity(P,[(Um,Vm)|MS]) :-
        !, dfs_init_g((Um,Vm),G),
        dfs_interpret(P,(Um,Vm),G),
        dfs_validity(P,MS).
dfs_validity(P,MM) :-
        dfs_matrix_to_models(MM,MS),
        dfs_validity(P,MS).

%% dfs_satisfiability(+Formula,+ModelSet|+ModelMatrix)
%
%  A formula P is satisfiable iff:
%
%       P is true in at least one model M

dfs_satisfiability(_,[]) :- !, false.
dfs_satisfiability(P,[(Um,Vm)|MS]) :-
        !, dfs_init_g((Um,Vm),G),
        (  dfs_interpret(P,(Um,Vm),G)
        -> true
        ;  dfs_satisfiability(P,MS) ).
dfs_satisfiability(P,MM) :-
        dfs_matrix_to_models(MM,MS),
        dfs_satisfiability(P,MS).

%% dfs_entailment(+Formula,+ModelSet|+ModelMatrix)
% 
%  A formula P entails a formula Q (P |= Q) iff:
%
%       Q is true in every model that satisfies P.

dfs_entailment(_,_,[]) :- !, true.
dfs_entailment(P,Q,[(Um,Vm)|MS]) :-
        !, dfs_init_g((Um,Vm),G),
        dfs_interpret(imp(P,Q),(Um,Vm),G),
        dfs_entailment(P,Q,MS).
dfs_entailment(P,MM) :-
        dfs_matrix_to_models(MM,MS),
        dfs_entailment(P,MS).

%% dfs_logical_equivalence(+Formula,+ModelSet|+ModelMatrix)
%
%  A formula P is logically equivalent to formula Q iff:
%
%       [P]^M,g = [Q]^M,g for all models M and variable assignments g

dfs_logical_equivalence(_,_,[]) :- !, true.
dfs_logical_equivalence(P,Q,[(Um,Vm)|MS]) :-
        !, dfs_init_g((Um,Vm),G),
        dfs_interpret(iff(P,Q),(Um,Vm),G),
        dfs_logical_equivalence(P,Q,MS).
dfs_logical_equivalence(P,MM) :-
        dfs_matrix_to_models(MM,MS),
        dfs_logical_equivalence(P,MS).
