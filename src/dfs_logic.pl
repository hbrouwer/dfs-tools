/*
 * dfs_logic.pl
 *
 * Copyright 2017 Harm Brouwer <me@hbrouwer.eu>
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
                conjoin/2,
                disjoin/2,
                complement/2,
                conj_vector/3
        ]).

/** <module> First-order Logic

This module implements basic first-order logic operations on formulas and
vectors.
*/

%!      conjoin(+FormulaSet,-Conjunction) is det.
%
%       True if Conjunction is a logical conjunction of the formulas in
%       FormulaSet.

conjoin([],[]).
conjoin([P],P) :- !.
conjoin([P|Ps],and(P,F)) :-
        conjoin(Ps,F).

%!      disjoin(+FormulaSet,-Disjunction) is det.
%
%       True if Disjunction is a logical disjunction of the formulas in
%       FormulaSet.

disjoin([],[]).
disjoin([P],P) :- !.
disjoin([P|Ps],or(P,F)) :-
        disjoin(Ps,F).

%!      complement(+Formula,+ComplementFormula)
%
%       ComplementFormula is specifies the falsehood conditions of Formula.

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
complement(exor(P0,Q0),or(and(P1,Q1),and(neg(P1),neg(Q1)))) :-
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

%!      conj_vector(+Vector1,+Vector2,-ConjVector) is det.
%
%       ConjVector is the conjunction (component-wise product) of Vector1
%       and Vector2.

conj_vector([],[],[]).
conj_vector([U0|U0s],[U1|U1s],[U2|U2s]) :-
        U2 is U0 * U1,
        conj_vector(U0s,U1s,U2s).
