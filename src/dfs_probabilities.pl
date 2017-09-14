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
                dfs_prior_probability/3,
                dfs_conj_probability/4,
                dfs_cond_probability/4,
                dfs_inference_score/4
        ]).

:- use_module(dfs_vector_space).

% dfs_prior_probability(+Formula,+ModelSet|+ModelMatrix,-PriorPr)

dfs_prior_probability(P,Ms,Pr) :-
        !, dfs_vector(P,Ms,V),
        sum_list(V,S),
        length(V,L),
        Pr is S / L.

% dfs_prior_probability(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-ConjPr)

dfs_conj_probability(P,P,Ms,Pr) :-
        !, dfs_prior_probability(P,Ms,Pr).
dfs_conj_probability(P,Q,Ms,Pr) :-
        dfs_prior_probability(and(P,Q),Ms,Pr).

% dfs_prior_probability(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-CondPr)

dfs_cond_probability(P,Q,Ms,Pr) :-
        dfs_conj_probability(P,Q,Ms,PrPQ),
        dfs_prior_probability(Q,Ms,PrP),
        (  PrP > 0
        -> Pr is PrPQ / PrP
        ;  Pr is nan ).

% dfs_inference_score(+Formula1,Formula2,+ModelSet|+ModelMatrix,-Score)

dfs_inference_score(P,Q,Ms,CS) :-
        dfs_cond_probability(P,Q,Ms,PrPQ),
        dfs_prior_probability(P,Ms,PrQ),
        (  PrQ > 0
        -> (  PrPQ > PrQ
           -> CS is (PrPQ - PrQ) / (1 - PrQ)
           ;  CS is (PrPQ - PrQ) / PrQ )
        ;  CS is nan ).
