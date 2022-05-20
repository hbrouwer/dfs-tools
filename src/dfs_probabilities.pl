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

:- module(dfs_probabilities,
        [
                dfs_prior_probability/2,
                dfs_prior_probability/3,
                dfs_conj_probability/3,
                dfs_conj_probability/4,
                dfs_cond_probability/3,
                dfs_cond_probability/4,
                dfs_inference_score/3,
                dfs_inference_score/4
        ]).

:- use_module(library(lists)).

:- use_module(dfs_logic).
:- use_module(dfs_vector_space).

/** <module> Probabilities

Probabilities of formulas given a set of models.
*/

%!      dfs_prior_probability(+Vector,-PriorPr) is det.
%!      dfs_prior_probability(+Formula,+ModelSet,-PriorPr) is det.
%!      dfs_prior_probability(+Formula,+ModelMatrix,-PriorPr) is det.
%
%       Prior probability of P, where P is either a vector or a formula.
%
%       ==
%       Pr(P) = sum_i(v_i(P)) / |M|
%       ==

dfs_prior_probability(VP,Pr) :-
        sum_list(VP,S),
        length(VP,M),
        Pr is S / M.

dfs_prior_probability(P,Ms,Pr) :-
        dfs_vector(P,Ms,VP),
        dfs_prior_probability(VP,Pr).

%!      dfs_conj_probability(+Vector1,+Vector2,-ConjPr) is det.
%!      dfs_conj_probability(+Formula1,+Formula2,+ModelSet,-ConjPr) is det.
%!      dfs_conj_probability(+Formula1,+Formula2,+ModelMatrix,-ConjPr) is det.
%
%       Conjunction probability of P and Q, where P and Q are either vectors or formulas.
%
%       ==
%       Pr(P&Q) = sum_i(v_i(P&Q)) / |M|
%       ==


dfs_conj_probability(VP,VQ,Pr) :-
        dfs_conj_vector(VP,VQ,VPaQ),
        dfs_prior_probability(VPaQ,Pr).

dfs_conj_probability(P,Q,Ms,Pr) :-
        dfs_prior_probability(and(P,Q),Ms,Pr).

%!      dfs_cond_probability(+Vector1,Vector2,-ConjPr) is det.
%!      dfs_cond_probability(+Formula1,+Formula2,+ModelSet,-CondPr) is det.
%!      dfs_cond_probability(+Formula1,+Formula2,+ModelMatrix,-CondPr) is det.
%
%       Conditional probability of P given Q, where P and Q are either vectors or formulas.
%       
%       ==
%       Pr(P|Q) = Pr(P&Q) / Pr(Q)
%       ==

dfs_cond_probability(VP,VQ,Pr) :-
        dfs_conj_probability(VP,VQ,PrPaQ),
        dfs_prior_probability(VQ,PrQ),
        dfs_cond_probability_(PrPaQ,PrQ,Pr).

dfs_cond_probability(P,Q,Ms,Pr) :-
        dfs_conj_probability(P,Q,Ms,PrPaQ),
        dfs_prior_probability(Q,Ms,PrQ),
        dfs_cond_probability_(PrPaQ,PrQ,Pr).

dfs_cond_probability_(PrPaQ,PrQ,Pr) :-
        (  PrQ > 0
        -> Pr is PrPaQ / PrQ
        ;  Pr is nan ).

%!      dfs_inference_score(+Vector1,+Vector2,-Score) is det.
%!      dfs_inference_score(+Formula1,+Formula2,+ModelSet,-Score) is det.
%!      dfs_inference_score(+Formula1,+Formula2,+ModelMatrix,-Score) is det.
%
%       Inference score of P from Q, where P and Q are either vectors or formulas.
%
%       ==
%                  | (Pr(P|Q) - Pr(P)) / (1 - Pr(P))    iff Pr(P|Q) > Pr(P)
%       inf(P,Q) = |
%                  | (Pr(P|Q) - Pr(P)) / Pr(P)          otherwise
%       ==

dfs_inference_score(VP,VQ,IS) :-
        dfs_cond_probability(VP,VQ,PrPgQ),
        dfs_prior_probability(VP,PrP),      
        dfs_inference_score_(PrPgQ,PrP,IS).

dfs_inference_score(P,Q,Ms,IS) :-
        dfs_cond_probability(P,Q,Ms,PrPgQ),
        dfs_prior_probability(P,Ms,PrP),
        dfs_inference_score_(PrPgQ,PrP,IS).

dfs_inference_score_(PrPgQ,PrP,IS) :-
        (  PrP > 0
        -> (  PrPgQ > PrP
           -> IS is (PrPgQ - PrP) / (1.0 - PrP)
           ;  IS is (PrPgQ - PrP) / PrP )
        ;  IS is nan ).
