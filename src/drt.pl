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

:- module(drt,
        [
                drs_to_fol/2,
                drs_interpret/3
        ]).

%!      drs_to_fol(+DRS,-Formula) is det.
%
%       Translate DRS into a first-order logic Formula. 

drs_to_fol(drs([],CK),F) :-
        drs_conditions_to_fol(CK,F).
drs_to_fol(drs([R|UK],CK),exists(R,F)) :-
        drs_to_fol(drs(UK,CK),F).

%!      drs_conditions_to_fol(+Condtions,-Formula) is det.
%
%       Translate DRS into a first-order logic Formula. 

drs_conditions_to_fol([],top).
drs_conditions_to_fol([P],F) :-
        !, % P
        drs_condition_to_fol(P,F).
drs_conditions_to_fol([P|CK],and(F1,F2)) :-
        % P & ...
        drs_condition_to_fol(P,F1),
        drs_conditions_to_fol(CK,F2).

drs_condition_to_fol(T1=T2,T1=T2) :- 
        !. % t1 = t2
drs_condition_to_fol(neg(K),neg(F)) :-
        !, % ![UK|CK]
        drs_to_fol(K,F).
drs_condition_to_fol(or(K1,K2),or(F1,F2)) :-
        !, % [UK1|CK1] | [UK2|CK2]
        drs_to_fol(K1,F1),
        drs_to_fol(K2,F2).
drs_condition_to_fol(imp(K1,K2),F) :-
        !, % [UK1|CK1] => [UK2|CK2]
        drs_imp_to_fol(imp(K1,K2),F).
drs_condition_to_fol(P,P) :-
        !. % R(t1,...,tn)

%!      drs_imp_to_fol(+DRS1,+DRS2,-Formula) is det.
%
%       Translate DRS1 and DRS2 to a universally quantified
%       implication. 

drs_imp_to_fol(imp(drs([],CK1),K2),imp(F1,F2)) :-
        !, drs_conditions_to_fol(CK1,F1),
        drs_to_fol(K2,F2).
drs_imp_to_fol(imp(drs([R|UK1],CK1),K2),forall(R,F)) :-
        drs_imp_to_fol(imp(drs(UK1,CK1),K2),F).

%!      drs_interpret(+DRS,+ModelSet,-Vector) is det.
%!      drs_interpret(+DRS,+ModelMatrix,-Vector) is det.
%
%       A DRS K is true in a model M iff [[K]]^M,g = 1 given an arbitrary
%       variable assignment g.

drs_interpret(K,MS,V) :-
        drs_to_fol(K,F),
        dfs_vector(F,MS,V).
