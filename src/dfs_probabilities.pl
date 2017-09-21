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
                dfs_inference_score/4,
                dfs_surprisal/4,
                dfs_delta_entropy/4,
                dfs_entropy/3
        ]).

:- use_module(dfs_vector_space).

%% dfs_prior_probability(+Formula,+ModelSet|+ModelMatrix,-PriorPr)
%
%  Pr(P) = |{i|v_i(P) = 1}| / |M|

dfs_prior_probability(P,Ms,Pr) :-
        dfs_vector(P,Ms,V),
        sum_list(V,S),
        length(V,L),
        Pr is S / L.

%% dfs_prior_probability(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-ConjPr)
%
%            | Pr(P)    iff P = Q
%  Pr(P&Q) = |
%            | Pr(P&Q)  otherwise

dfs_conj_probability(P,P,Ms,Pr) :-      %% P = Q
        !, dfs_prior_probability(P,Ms,Pr).
dfs_conj_probability(P,Q,Ms,Pr) :-      %% P != Q
        dfs_prior_probability(and(P,Q),Ms,Pr).

%% dfs_prior_probability(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-CondPr)
%
%  Pr(P|Q) = Pr(P&Q) / Pr(P)

dfs_cond_probability(P,Q,Ms,Pr) :-
        dfs_conj_probability(P,Q,Ms,PrPQ),
        dfs_prior_probability(Q,Ms,PrP),
        (  PrP > 0
        -> Pr is PrPQ / PrP
        ;  Pr is nan ).

%% dfs_inference_score(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-Score)
%
%                   | (Pr(P&Q) - P(Q)) / (1 - Pr(Q))    iff Pr(P&Q) > Pr(Q)  
%  inference(P,Q) = |
%                   | (Pr(P&Q) - P(Q)) / Pr(Q)          otherwise

dfs_inference_score(P,Q,Ms,IS) :-
        dfs_cond_probability(P,Q,Ms,PrPQ),
        dfs_prior_probability(P,Ms,PrQ),
        (  PrQ > 0
        -> (  PrPQ > PrQ
           -> IS is (PrPQ - PrQ) / (1 - PrQ)
           ;  IS is (PrPQ - PrQ) / PrQ )
        ;  IS is nan ).

%% dfs_surprisal(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-Surprisal)
%
%  surprisal(P,Q) = -log(P|Q)

dfs_surprisal(P,Q,Ms,S) :-
        dfs_cond_probability(P,Q,Ms,PrPQ),
        (  PrPQ > 0.0
        -> S is -log(PrPQ)
        ;  S is inf ).

%% dfs_delta_entropy(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-EntropyDelta)
%
%  DH(P,Q) = H(Q) - H(P)

dfs_delta_entropy(P,Q,Ms,DH) :-
        dfs_entropy(P,Ms,Hnew),
        dfs_entropy(Q,Ms,Hold),
        DH is Hold - Hnew.

%% dfs_entropy(+Formula,+ModelSet|+ModelMatrix,-Entropy)
%
%  H(P) = -sum_{s in S} P(s|P) * log(s|P)
%
%  where the set S conststs of all possible points in the DFS space that are
%  fully specified with respsect to the atomic propositions; that is, eachq
%  point s in S constitutes a unique logical combination of all atomic
%  propostions.

dfs_entropy(P,Ms,H) :-
        dfs_vector(P,Ms,V),
        sum_list(V,S),
        length(V,L),
        PrP is S / L,
        dfs_entropy_(V,PrP,0,H).

dfs_entropy_([],_,HAcc,H) :-
        !, H is -HAcc.
dfs_entropy_([U|Us],PrP,HAcc,H) :-
        PrUQ is (1.0 * U) / PrP,
        (  PrUQ > 0.0
        -> HAcc0 is HAcc + PrUQ * log(PrUQ)
        ;  HAcc0 is HAcc ),
        dfs_entropy_(Us,PrP,HAcc0,H).
