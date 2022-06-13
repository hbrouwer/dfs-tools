/*
 * Copyright 2017-2022 Harm Brouwer <me@hbrouwer.eu>
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
                drs_to_rfol/2,
                drs_interpret/3
        ]).

%!      drs_to_fol(+DRS,-Formula) is det.
%
%       Translate DRS into a first-order logic Formula. 

drs_to_fol(drs([],CK),F) :-
        drs_conditions_to_fol(CK,false,F).
drs_to_fol(drs([R|UK],CK),exists(R,F)) :-
        drs_to_fol(drs(UK,CK),F).

%!      drs_to_rfol(+DRS,-Formula) is det.
%
%       Translate DRS into a referential first-order logic Formula. 

drs_to_rfol(drs([],CK),F) :-
        drs_conditions_to_fol(CK,true,F).
drs_to_rfol(drs([R|UK],CK),exists(R,and(referent(R),F))) :-
        drs_to_rfol(drs(UK,CK),F).

%!      drs_conditions_to_fol(+Conditions,+AssertRefs,-Formula) is det.
%
%       Translate DRS into a first-order logic Formula. If AssertRefs ==
%       True, referents will be asserted using a referent/1 predicate.

drs_conditions_to_fol([],_,top).
drs_conditions_to_fol([P],ARs,F) :-
        !, % P
        drs_condition_to_fol(P,ARs,F).
drs_conditions_to_fol([P|CK],ARs,and(F1,F2)) :-
        % P & ...
        drs_condition_to_fol(P,ARs,F1),
        drs_conditions_to_fol(CK,ARs,F2).

drs_condition_to_fol(T1=T2,_,T1=T2) :- 
        !. % t1 = t2
drs_condition_to_fol(neg(K),ARs,neg(F)) :-
        !, % ![UK|CK]
        (  ARs == false
        -> drs_to_fol(K,F)
        ;  drs_to_rfol(K,F) ).
drs_condition_to_fol(or(K1,K2),ARs,or(F1,F2)) :-
        !, % [UK1|CK1] | [UK2|CK2]
        (  ARs == false
        -> drs_to_fol(K1,F1),
           drs_to_fol(K2,F2)
        ;  drs_to_rfol(K1,F1),
           drs_to_rfol(K2,F2) ). 
drs_condition_to_fol(imp(K1,K2),ARs,F) :-
        !, % [UK1|CK1] => [UK2|CK2]
        (  ARs == false
        -> drs_imp_to_fol(imp(K1,K2),F)
        ;  drs_imp_to_rfol(imp(K1,K2),F) ).
drs_condition_to_fol(P,_,P) :-
        !. % R(t1,...,tn)

%!      drs_imp_to_fol(+DRS1,+DRS2,-Formula) is det.
%
%       Translate DRS1 and DRS2 to a universally quantified
%       implication. 

drs_imp_to_fol(imp(drs([],CK1),K2),imp(F1,F2)) :-
        !, drs_conditions_to_fol(CK1,false,F1),
        drs_to_fol(K2,F2).
drs_imp_to_fol(imp(drs([R|UK1],CK1),K2),forall(R,F)) :-
        drs_imp_to_fol(imp(drs(UK1,CK1),K2),F).

%!      drs_imp_to_rfol(+DRS1,+DRS2,-Formula) is det.
%
%       Translate DRS1 and DRS2 to a universally quantified
%       referential implication. 

drs_imp_to_rfol(imp(drs([],CK1),K2),imp(F1,F2)) :-
        !, drs_conditions_to_fol(CK1,true,F1),
        drs_to_rfol(K2,F2).
drs_imp_to_rfol(imp(drs([R|UK1],CK1),K2),forall(R,imp(referent(R),F))) :-
        drs_imp_to_rfol(imp(drs(UK1,CK1),K2),F).

%!      drs_interpret(+DRS,+ModelSet,-Vector) is det.
%!      drs_interpret(+DRS,+ModelMatrix,-Vector) is det.
%
%       A DRS K is true in a model M iff [[K]]^M,g = 1 given an arbitrary
%       variable assignment g.

drs_interpret(K,MS,V) :-
        drs_to_fol(K,F),
        dfs_vector(F,MS,V).
