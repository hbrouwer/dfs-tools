/*
 * Copyright 2017-2018 Harm Brouwer <me@hbrouwer.eu>
 *     and Noortje Venhuizen <njvenhuizen@gmail.com>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

:- module(dfs_logic,
        [
                dfs_conjoin/2,
                dfs_disjoin/2,
                dfs_complement/2,
                dfs_conj_vector/3,
                dfs_validity/2,
                dfs_satisfiability/2,
                dfs_entailment/3,
                dfs_logical_equivalence/3
        ]).

:- use_module(dfs_interpretation).
:- use_module(dfs_vector_space).

/** <module> First-order Logic

This module implements basic first-order logic operations and properties on 
formulas and vectors.
*/

%!      dfs_conjoin(+FormulaSet,-Conjunction) is det.
%
%       True if Conjunction is a logical conjunction of the formulas in
%       FormulaSet.

dfs_conjoin([],[]).
dfs_conjoin([P],P) :- !.
dfs_conjoin([P|Ps],and(P,F)) :-
        dfs_conjoin(Ps,F).

%!      dfs_disjoin(+FormulaSet,-Disjunction) is det.
%
%       True if Disjunction is a logical disjunction of the formulas in
%       FormulaSet.

dfs_disjoin([],[]).
dfs_disjoin([P],P) :- !.
dfs_disjoin([P|Ps],or(P,F)) :-
        dfs_disjoin(Ps,F).

%!      dfs_complement(+Formula,+ComplementFormula) is det.
%
%       ComplementFormula specifies the falsehood conditions of Formula.

dfs_complement(neg(P0),neg(P1)) :-
        !, % !P => !P
        dfs_complement(P0,P1).
dfs_complement(and(P0,Q0),or(P1,Q1)) :-
        !, % P & Q => P | Q
        dfs_complement(P0,P1),
        dfs_complement(Q0,Q1).
dfs_complement(or(P0,Q0),and(P1,Q1)) :-
        !, % P | Q => P & Q
        dfs_complement(P0,P1),
        dfs_complement(Q0,Q1).
dfs_complement(exor(P0,Q0),or(and(P1,Q1),and(neg(P1),neg(Q1)))) :-
        !, % P (+) Q => (P & Q) | (!P & !Q)
        dfs_complement(P0,P1),
        dfs_complement(Q0,Q1). 
dfs_complement(imp(P0,Q0),and(neg(P1),Q1)) :-
        !, % P -> Q => !P & Q
        dfs_complement(P0,P1),
        dfs_complement(Q0,Q1).
dfs_complement(iff(P0,Q0),or(and(neg(P1),Q1),and(P1,neg(Q1)))) :-
        !, % P <-> Q => (!P & Q) | (P & !Q)
        dfs_complement(P0,P1),
        dfs_complement(Q0,Q1).
dfs_complement(exists(X,P0),forall(X,P1)) :-
        !, % ∃x P => ∀x P
        dfs_complement(P0,P1).
dfs_complement(forall(X,P0),exists(X,P1)) :-
        !, % ∀x P => ∃x P
        dfs_complement(P0,P1).
dfs_complement(P,P).

                %%%%%%%%%%%%%%%%%
                %%%% vectors %%%%
                %%%%%%%%%%%%%%%%%

%!      dfs_conj_vector(+Vector1,+Vector2,-ConjVector) is det.
%
%       ConjVector is the conjunction (component-wise product) of Vector1
%       and Vector2.

dfs_conj_vector([],[],[]).
dfs_conj_vector([U0|U0s],[U1|U1s],[U2|U2s]) :-
        U2 is U0 * U1,
        dfs_conj_vector(U0s,U1s,U2s).

                %%%%%%%%%%%%%%%%%%%%
                %%%% properties %%%%
                %%%%%%%%%%%%%%%%%%%%

%!      dfs_validity(+Formula,+ModelSet) is det.
%!      dfs_validity(+Formula,+ModelMatrix) is det.
%
%       A formula P is valid (|= P) iff P is true (not false) in all models.

dfs_validity(_,[]) :- !.
dfs_validity(P,[(Um,Vm)|MS]) :-
        !, dfs_init_g((Um,Vm),G),
        dfs_interpret(P,(Um,Vm),G),
        dfs_validity(P,MS).
dfs_validity(P,MM) :-
        dfs_matrix_to_models(MM,MS),
        dfs_validity(P,MS).

%!      dfs_satisfiability(+Formula,+ModelSet) is det.
%!      dfs_satisfiability(+Formula,+ModelMatrix) is det.
%
%       A formula P is satisfiable iff P is true in at least one model M.

dfs_satisfiability(_,[]) :- !, false.
dfs_satisfiability(P,[(Um,Vm)|MS]) :-
        !, dfs_init_g((Um,Vm),G),
        (  dfs_interpret(P,(Um,Vm),G)
        -> true
        ;  dfs_satisfiability(P,MS) ).
dfs_satisfiability(P,MM) :-
        dfs_matrix_to_models(MM,MS),
        dfs_satisfiability(P,MS).

%!      dfs_entailment(+Formula,+ModelSet) is det.
%!      dfs_entailment(+Formula,+ModelMatrix) is det.
% 
%       A formula P entails a formula Q (P |= Q) iff Q is true in every model
%       that satisfies P.

dfs_entailment(_,_,[]) :- !.
dfs_entailment(P,Q,[(Um,Vm)|MS]) :-
        !, dfs_init_g((Um,Vm),G),
        dfs_interpret(imp(P,Q),(Um,Vm),G),
        dfs_entailment(P,Q,MS).
dfs_entailment(P,Q,MM) :-
        dfs_matrix_to_models(MM,MS),
        dfs_entailment(P,Q,MS).

%!      dfs_logical_equivalence(+Formula,+ModelSet) is det.
%!      dfs_logical_equivalence(+Formula,+ModelMatrix) is det.
%
%       A formula P is logically equivalent to formula Q iff [P]^M,g = [Q]^M,g
%       for all models M and variable assignments g

dfs_logical_equivalence(_,_,[]) :- !.
dfs_logical_equivalence(P,Q,[(Um,Vm)|MS]) :-
        !, dfs_init_g((Um,Vm),G),
        dfs_interpret(iff(P,Q),(Um,Vm),G),
        dfs_logical_equivalence(P,Q,MS).
dfs_logical_equivalence(P,Q,MM) :-
        dfs_matrix_to_models(MM,MS),
        dfs_logical_equivalence(P,Q,MS).

