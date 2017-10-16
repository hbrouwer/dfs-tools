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

%% dfs_prior_probability(+Vector,-PriorPr)
%  dfs_prior_probability(+Formula,+ModelSet|+ModelMatrix,-PriorPr)
%
%  Pr(P) = |{i|v_i(P) = 1}| / |M|

dfs_prior_probability(V,Pr) :-
        sum_list(V,S),
        length(V,L),
        Pr is S / L.

dfs_prior_probability(P,Ms,Pr) :-
        dfs_vector(P,Ms,V),
        dfs_prior_probability(V,Pr).

%% dfs_conj_probability(+Vector1,Vector2,-ConjPr)
%  dfs_conj_probability(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-ConjPr)
%
%            | Pr(P)    iff P = Q
%  Pr(P&Q) = |
%            | Pr(P&Q)  otherwise

dfs_conj_probability(V,V,Pr) :-         %% V0 = V1
        !, dfs_prior_probability(V,Pr).
dfs_conj_probability(V0,V1,Pr) :-       %% V0 != V!
        dfs_conj_probability_(V0,V1,V2),
        dfs_prior_probability(V2,Pr).

dfs_conj_probability(P,P,Ms,Pr) :-      %% P = Q
        !, dfs_prior_probability(P,Ms,Pr).
dfs_conj_probability(P,Q,Ms,Pr) :-      %% P != Q
        dfs_prior_probability(and(P,Q),Ms,Pr).

dfs_conj_probability_([],[],[]).
dfs_conj_probability_([U0|U0s],[U1|U1s],[U2|U2s]) :-
        U2 is U0 * U1,
        dfs_conj_probability_(U0s,U1s,U2s).

%% dfs_cond_probability(+Vector1,Vector2,-ConjPr)
%  dfs_cond_probability(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-CondPr)
%
%  Pr(P|Q) = Pr(P&Q) / Pr(P)

dfs_cond_probability(V0,V1,Pr) :-
        dfs_conj_probability(V0,V1,PrV0V1),
        dfs_prior_probability(V1,PrV0),
        dfs_cond_probability_(PrV0V1,PrV0,Pr).

dfs_cond_probability(P,Q,Ms,Pr) :-
        dfs_conj_probability(P,Q,Ms,PrPQ),
        dfs_prior_probability(Q,Ms,PrP),
        dfs_cond_probability_(PrPQ,PrP,Pr).

dfs_cond_probability_(PrPQ,PrP,Pr) :-
        (  PrP > 0
        -> Pr is PrPQ / PrP
        ;  Pr is nan ).

%% dfs_inference_score(+Vector1,+Vector2,-Score)
%  dfs_inference_score(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-Score)
%
%                   | (Pr(P&Q) - P(Q)) / (1 - Pr(Q))    iff Pr(P&Q) > Pr(Q)  
%  inference(P,Q) = |
%                   | (Pr(P&Q) - P(Q)) / Pr(Q)          otherwise

dfs_inference_score(V0,V1,IS) :-
        dfs_cond_probability(V0,V1,PrV0V1),
        dfs_prior_probability(V1,PrV1),      
        dfs_inference_score_(PrV0V1,PrV1,IS).

dfs_inference_score(P,Q,Ms,IS) :-
        dfs_cond_probability(P,Q,Ms,PrPQ),
        dfs_prior_probability(P,Ms,PrQ),
        dfs_inference_score_(PrPQ,PrQ,IS).

dfs_inference_score_(PrPQ,PrQ,IS) :-
        (  PrQ > 0
        -> (  PrPQ > PrQ
           -> IS is (PrPQ - PrQ) / (1 - PrQ)
           ;  IS is (PrPQ - PrQ) / PrQ )
        ;  IS is nan ).
