/*
 * Copyright 2017-2021 Harm Brouwer <me@hbrouwer.eu>
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

 :- module(dfs_semantics,
        [
                dfs_semantics/3,
                dfs_entailments/3,
                dfs_coordinates/2
        ]).

:- use_module(library(clpfd)).

/** <module> DFS semantics

Interpretation of (sub-)propositional meaning as a set of points in DFS space.
*/

%!      dfs_semantics(+Formula,+ModelSet,-Interpretation) is semidet.
%
%       Derives an Interpretation (a set of points in DFS space) for Formula
%       given ModelSet.

dfs_semantics(neg(I0),MS,I2) :-
        !, % !{I_1 ... I_n}
        dfs_semantics(I0,MS,I1),
        dset_neg(I1,I2).
dfs_semantics(and(I0,I1),MS,I4) :-
        !, % {I_1 ... I_i} & {I_j ... I_n}
        dfs_semantics(I0,MS,I2),
        dfs_semantics(I1,MS,I3),
        dset_and(I2,I3,I4).
dfs_semantics(or(I0,I1),MS,I4) :-
        !, % {I_1 ... I_i} | {I_j ... I_n}
        dfs_semantics(I0,MS,I2),
        dfs_semantics(I1,MS,I3),
        dset_or(I2,I3,I4).
dfs_semantics(exor(I0,I1),MS,I4) :-
        !, % {I_1 ... I_i} (+) {I_j ... I_n}
        dfs_semantics(I0,MS,I2),
        dfs_semantics(I1,MS,I3),
        dset_exor(I2,I3,I4).
dfs_semantics(imp(I0,I1),MS,I4) :-
        !, % {I_1 ... I_i} --> {I_j ... I_n}
        dfs_semantics(I0,MS,I2),
        dfs_semantics(I1,MS,I3),
        dset_imp(I2,I3,I4).
dfs_semantics(iff(I0,I1),MS,I4) :-
        !, % {I_1 ... I_i} <-> {I_j ... I_n}
        dfs_semantics(I0,MS,I2),
        dfs_semantics(I1,MS,I3),
        dset_iff(I2,I3,I4).
dfs_semantics(merge(I0,I1),MS,I4) :-
        !, % {I_1 ... I_i} + {I_j ... I_n}
        dfs_semantics(I0,MS,I2),
        dfs_semantics(I1,MS,I3),
        dset_merge(I2,I3,I4).
dfs_semantics(W,MS,LI) :-
        atom(W),
        !, % lexical item
        lexical_semantics(W,MS,LI).
dfs_semantics(I,MS,I) :-
        % {I_1 ... I_i} = {I_1 ... I_i}
        foreach(member(V,I),is_meaning_vector(V,MS)).

%!      lexical_semantics(+Word,+ModelSet,-Interpretation) is semidet.
%
%       Derives an Interpretation for Word given ModelSet.

lexical_semantics(W,MS,I) :-
        dfs_vector_space:atomic_propositions(MS,APs),
        lexical_semantics_(APs,W,MS,I).

lexical_semantics_([],_,_,[]).
lexical_semantics_([AP|APs],W,MS,[I|Is]) :-
        AP =.. Ws,
        memberchk(W,Ws), !,
        dfs_vector(AP,MS,I),
        lexical_semantics_(APs,W,MS,Is).
lexical_semantics_([_|APs],W,MS,Is) :-
        lexical_semantics_(APs,W,MS,Is).

%!      is_meaning_vector(+Vector,+ModelSet) is semidet.
%
%       True iff Vector is a proper meaning vector in the semantic space
%       defined by ModelSet.

is_meaning_vector(V,MS) :-
        length(MS,L),
        length(V,L),
        foreach(member(U,V),(U == 0 ; U == 1)).

                %%%%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% logical operators %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%%%
        
%%%% negation %%%%

%!      dset_neg(+Prejacent,-Interpretation) is semidet.
%
%       Interpretation is the negation of Prejacent.

dset_neg(I0,[I2]) :-
        dset_neg_(I0,I1),
        conjunctive_closure(I1,I2).

dset_neg_([],[]).
dset_neg_([I0|Is0],[I1|Is1]) :-
        vect_neg(I0,I1),
        dset_neg_(Is0,Is1).

%!      vect_neg(+Vector1,-Vector2) is semidet.
%
%       Vector2 is the pointwise negation of Vector1.

vect_neg([],[]).
vect_neg([U0|Us0],[U1|Us1]) :-
        unit_neg(U0,U1),
        vect_neg(Us0,Us1).

%!      unit_neg(+Unit1,-Unit2) is semidet.
%
%       Unit2 is the negation of Unit1.

unit_neg(1,0) :- !.
unit_neg(0,1).

%%%% conjunction %%%%

%!      dset_and(+Conjunct1,+Conjunct2,-Interpretation) is semidet.
%
%       Interpretation is the conjunction of Conjunct1 and Conjunct2.

dset_and(Is0,Is1,Is2) :-
        findall(I,(member(I0,Is0),member(I1,Is1),vect_and(I0,I1,I)),Is2).

%!      vect_and(+Vector1,+Vector2,-Vector3) is semidet.
%
%       Vector3 is the pointwise conjunction of Vector1 and Vector2.

vect_and([],[],[]).
vect_and([U0|Us0],[U1|Us1],[U2|Us2]) :-
        unit_and(U0,U1,U2),
        vect_and(Us0,Us1,Us2).

%!      unit_and(+Unit1,+Unit2,-Unit3) is semidet.
%
%       Unit3 is the conjunction of Unit1 and Unit2.

unit_and(1,1,1) :- !.
unit_and(1,0,0) :- !.
unit_and(0,1,0) :- !.
unit_and(0,0,0) :- !.

%!      conjunctive_closure(+Interpretation,-CClosure) is semidet.
%
%       CClosure is the conjunctive closure over the constituents of
%       Interpretation.

conjunctive_closure([CC],CC) :- !.
conjunctive_closure([I0,I1|Is],CC) :-
        vect_and(I0,I1,I2),
        conjunctive_closure([I2|Is],CC).

%%%% disjunction %%%%

%!      dset_or(+Disjunct1,+Disjunct2,-Interpretation) is semidet.
%
%       Interpretation is the disjunction of Disjunct1 and Disjunct2.

dset_or(Is0,Is1,Is2) :-
        % findall(I,(member(I0,Is0),member(I1,Is1),vect_or(I0,I1,I)),Is2).
        union(Is0,Is1,Is2).

%!      vect_or(+Vector1,+Vector2,-Vector3) is semidet.
%
%       Vector3 is the pointwise disjunction of Vector1 and Vector2.

vect_or([],[],[]).
vect_or([U0|Us0],[U1|Us1],[U2|Us2]) :-
        unit_or(U0,U1,U2),
        vect_or(Us0,Us1,Us2).

%!      unit_or(+Unit1,+Unit2,-Unit3) is semidet.
%
%       Unit3 is the disjunction of Unit1 and Unit2.

unit_or(1,1,1) :- !.
unit_or(1,0,1) :- !.
unit_or(0,1,1) :- !.
unit_or(0,0,0).

%!      disjunctive_closure(+Interpretation,-DClosure) is semidet.
%
%       DClosure is the disjunctive closure over the constituents of
%       Interpretation.

disjunctive_closure([DC],DC) :- !.
disjunctive_closure([I0,I1|Is],DC) :-
        vect_or(I0,I1,I2),
        disjunctive_closure([I2|Is],DC).

%%%% exclusive disjunction %%%%

%!      dset_exor(+Disjunct1,+Disjunct2,-Interpretation) is semidet.
%
%       Interpretation is the exclusive disjunction of Disjunct1 and
%       Disjunct2.

dset_exor(Is0,Is1,Is2) :-
        findall(I,(member(I0,Is0),member(I1,Is1),vect_exor(I0,I1,I)),Is2).

%!      vect_exor(+Vector1,+Vector2,-Vector3) is semidet.
%
%       Vector3 is the pointwise exclusive disjunction of Vector1 and Vector2.

vect_exor([],[],[]).
vect_exor([U0|Us0],[U1|Us1],[U2|Us2]) :-
        unit_exor(U0,U1,U2),
        vect_exor(Us0,Us1,Us2).

%!      unit_exor(+Unit1,+Unit2,-Unit3) is semidet.
%
%       Unit3 is the exclusive disjunction of Unit1 and Unit2.

unit_exor(1,1,0) :- !.
unit_exor(1,0,1) :- !.
unit_exor(0,1,1) :- !.
unit_exor(0,0,0).

%%%% implication %%%%

%!      dset_imp(+Antecedent,+Consquent,-Interpretation) is semidet.
%
%       Interpretation is the implication between Antecedent and Consequent.

dset_imp(Is0,Is1,Is2) :-
        findall(I,(member(I0,Is0),member(I1,Is1),vect_imp(I0,I1,I)),Is2).

%!      vect_imp(+Vector1,+Vector2,-Vector3) is semidet.
%
%       Vector3 is the pointwise implication between Vector1 and Vector2.

vect_imp([],[],[]).
vect_imp([U0|Us0],[U1|Us1],[U2|Us2]) :-
        unit_imp(U0,U1,U2),
        vect_imp(Us0,Us1,Us2).

%!      unit_imp(+Unit1,+Unit2,-Unit3) is semidet.
%
%       Unit3 is the implication between Unit1 and Unit2.

unit_imp(1,1,1) :- !.
unit_imp(1,0,0) :- !.
unit_imp(0,1,1) :- !.
unit_imp(0,0,1).

%%%% equivalence %%%%

%!      dset_iff(+Prejacent1,+Prejacent2,-Interpretation) is semidet.
%
%       Interpretation is the equivalence between Prejacent1 and Prejacent2.

dset_iff(Is0,Is1,Is2) :-
        findall(I,(member(I0,Is0),member(I1,Is1),vect_iff(I0,I1,I)),Is2).

%!      vect_iff(+Vector1,+Vector2,-Vector3) is semidet.
%
%       Vector3 is the pointwise equivalence between Vector1 and Vector2.

vect_iff([],[],[]).
vect_iff([U0|Us0],[U1|Us1],[U2|Us2]) :-
        unit_iff(U0,U1,U2),
        vect_iff(Us0,Us1,Us2).

%!      unit_iff(+Unit1,+Unit2,-Unit3) is semidet.
%
%       Unit3 is the equivalence between Unit1 and Unit2.

unit_iff(1,1,1) :- !.
unit_iff(1,0,0) :- !.
unit_iff(0,1,0) :- !.
unit_iff(0,0,1).

%%%% merge %%%%

%!      dset_merge(+Context,+Assertion,-Interpretation) is semidet.
%
%       Interpretation is the merge of Assertion into Context.

dset_merge(Is0,Is1,Is3) :-
        disjunctive_closure(Is1,DC),
        findall(I0,(member(I0,Is0),vect_entails(I0,DC)),Is2),
        list_to_ord_set(Is2,Is3).

%!      vect_entails(+Vector1,+Vector2) is semidet.
%
%       True iff Vector1 pointwise entails Vector2.

vect_entails([],[]).
vect_entails([U0|Us0],[U1|Us1]) :-
        unit_entails(U0,U1,1),
        vect_entails(Us0,Us1).

%!      unit_entails(+Unit1,+Unit2) is semidet.
%
%       True iff Unit1 implies Unit2.

unit_entails(U0,U1,U2) :-
        unit_imp(U0,U1,U2).

                %%%%%%%%%%%%%%%%%%%%%%%%
                %%%% interpretation %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_entailments(+Interpretation,+ModelSet,-Entailments) is semidet.
%
%       Entailments is a set of (Element,AtomicProps) tuples, such that
%       each AtomicProps is a list of atomic propositions entailed by the
%       corresponding Element in Interpretation.

dfs_entailments(Is,MS,ETs) :-
        dfs_vector_space:atomic_propositions(MS,APs),
        findall((AP,APV),(member(AP,APs),dfs_vector(AP,MS,APV)),APTs),
        dfs_entailments_(Is,APTs,ETs).

dfs_entailments_([],_,[]).
dfs_entailments_([I|Is],APTs,[(I,ES)|ETs]) :-
        findall(EP,(member((EP,APV),APTs),vect_entails(I,APV)),ES),
        dfs_entailments_(Is,APTs,ETs).

%!      dfs_coordinates(+Interpretation,-Coordinates) is semidet.
%
%       Coordinates designates the point in space in between the elements of
%       Interpretation.

dfs_coordinates(I,Cs) :-
        transpose(I,[IT|ITs]),
        length(IT,ITL),
        dfs_coordinates_([IT|ITs],ITL,Cs).

dfs_coordinates_([],_,[]).
dfs_coordinates_([MV|MVs],MVL,[C|Cs]) :-
        sum_list(MV,Sum),
        C is Sum / MVL,
        dfs_coordinates_(MVs,MVL,Cs).
