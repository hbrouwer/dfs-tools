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

dfs_prior_probability(VP,Pr) :-
        sum_list(VP,S),
        length(VP,L),
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

dfs_conj_probability(VP,VP,Pr) :-       %% VP = VQ
        !, dfs_prior_probability(VP,Pr).
dfs_conj_probability(VP,VQ,Pr) :-       %% VP != VQ
        dfs_conj_probability_(VP,VQ,VPQ),
        dfs_prior_probability(VPQ,Pr).

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
%  Pr(P|Q) = Pr(P&Q) / Pr(Q)

dfs_cond_probability(VP,VQ,Pr) :-
        dfs_conj_probability(VP,VQ,PrPQ),
        dfs_prior_probability(VQ,PrQ),
        dfs_cond_probability_(PrPQ,PrQ,Pr).

dfs_cond_probability(P,Q,Ms,Pr) :-
        dfs_conj_probability(P,Q,Ms,PrPQ),
        dfs_prior_probability(Q,Ms,PrQ),
        dfs_cond_probability_(PrPQ,PrQ,Pr).

dfs_cond_probability_(PrPQ,PrQ,Pr) :-
        (  PrQ > 0
        -> Pr is PrPQ / PrQ
        ;  Pr is nan ).

%% dfs_inference_score(+Vector1,+Vector2,-Score)
%  dfs_inference_score(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-Score)
%
%                   | (Pr(P&Q) - P(P)) / (1 - Pr(P))    iff Pr(P&Q) > Pr(P)  
%  inference(P,Q) = |
%                   | (Pr(P&Q) - P(P)) / Pr(P)          otherwise

dfs_inference_score(VP,VQ,IS) :-
        dfs_cond_probability(VP,VQ,PrPQ),
        dfs_prior_probability(VP,PrP),      
        dfs_inference_score_(PrPQ,PrP,IS).

dfs_inference_score(P,Q,Ms,IS) :-
        dfs_cond_probability(P,Q,Ms,PrPQ),
        dfs_prior_probability(P,Ms,PrP),
        dfs_inference_score_(PrPQ,PrP,IS).

dfs_inference_score_(PrPQ,PrP,IS) :-
        (  PrP > 0
        -> (  PrPQ > PrP
           -> IS is (PrPQ - PrP) / (1.0 - PrP)
           ;  IS is (PrPQ - PrP) / PrP )
        ;  IS is nan ).
