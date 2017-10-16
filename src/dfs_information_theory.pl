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

:- module(dfs_information_theory,
        [
                dfs_surprisal/3,
                dfs_surprisal/4,
                dfs_entropy/2,
                dfs_entropy/3,
                dfs_delta_entropy/3,
                dfs_delta_entropy/4,
                dfs_syntactic_surprisal/3,
                dfs_syntactic_entropy/2,
                dfs_syntactic_delta_entropy/3,
                dfs_semantic_surprisal/4,
                dfs_semantic_entropy/3,
                dfs_semantic_delta_entropy/4,
                dfs_fapply_surprisal/4,
                dfs_fapply_entropy/3
                dfs_fapply_delta_entropy/4
        ]).

%% dfs_surprisal(+Vector1,+Vector2,-Surprisal)
%  dfs_surprisal(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-Surprisal)
%
%  surprisal(P,Q) = -log(P|Q)

dfs_surprisal(V0,V1,S) :-
        dfs_cond_probability(V0,V1,PrV0V1),
        dfs_surprisal_(PrV0V1,S).

dfs_surprisal(P,Q,Ms,S) :-
        dfs_cond_probability(P,Q,Ms,PrPQ),
        dfs_surprisal_(PrPQ,S).

dfs_surprisal_(PrPQ,S) :-
        (  PrPQ > 0.0
        -> S is -log(PrPQ)
        ;  S is inf ).     

%% dfs_entropy(+Vector,-Entropy) 
%  dfs_entropy(+Formula,+ModelSet|+ModelMatrix,-Entropy)
%
%  H(P) = -sum_{s in S} P(s|P) * log(s|P)
%
%  where the set S consists of all possible points in the DFS space that are
%  fully specified with respsect to the atomic propositions; that is, each
%  point s in S constitutes a unique logical combination of all atomic
%  propostions.

dfs_entropy(V,H) :-
        sum_list(V,S),
        dfs_entropy_(V,S,0,H).

dfs_entropy(P,Ms,H) :-
        dfs_vector(P,Ms,V),
        dfs_entropy(V,H).
        
dfs_entropy_([],_,HAcc,H) :-
        H is -HAcc.
dfs_entropy_([U|Us],S,HAcc,H) :-
        PrUQ is (1.0 * U) / S,
        (  PrUQ > 0.0
        -> HAcc0 is HAcc + PrUQ * log(PrUQ)
        ;  HAcc0 is HAcc ),
        dfs_entropy_(Us,S,HAcc0,H).

%% dfs_delta_entropy(+Vector1,+Vector2,-EntropyDelta)
%  dfs_delta_entropy(+Formula1,+Formula2,+ModelSet|+ModelMatrix,-EntropyDelta)
%
%  DH(P,Q) = H(Q) - H(P)

dfs_delta_entropy(V0,V1,DH) :-
        dfs_entropy(V0,Hnew),
        dfs_entropy(V1,Hold),
        DH is Hold - Hnew.

dfs_delta_entropy(P,Q,Ms,DH) :-
        dfs_entropy(P,Ms,Hnew),
        dfs_entropy(Q,Ms,Hold),
        DH is Hold - Hnew.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% experimental stuff %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% dfs_syntactic_surprisal(+Prefix,+Word,-Surprisal)

dfs_syntactic_surprisal(Prefix,W,S) :-
        append(Prefix,[W],PrefixW),
        dfs_prefix_frequency(Prefix, F),
        dfs_prefix_frequency(PrefixW,FW),
        S is log(F) - log(FW).

% dfs_syntactic_entropy(+Prefix,-Entropy).

dfs_syntactic_entropy(Prefix,H) :-
        dfs_prefix_continuations(Prefix,Cs),
        length(Cs,TF),
        list_to_ord_set(Cs,Cs0),
        dfs_syntactic_entropy_(Cs0,TF,0,H).

dfs_syntactic_entropy_([],_,H,H).
dfs_syntactic_entropy_([(C,_)|Cs],TF,HAcc,H) :-
        dfs_sentence_frequency(C,F),
        P is F / TF,
        HAcc0 is HAcc - P * log(P),
        dfs_syntactic_entropy_(Cs,TF,HAcc0,H).

% dfs_syntactic_delta_entropy(+Prefix,+Word,-DeltaEntropy).

dfs_syntactic_delta_entropy(Prefix,W,DH) :-
        append(Prefix,[W],PrefixW),
        dfs_syntactic_entropy(Prefix, H),
        dfs_syntactic_entropy(PrefixW,HW),
        DH is H - HW.

% dfs_semantic_surprisal(+Prefix,+Word,+ModelSet,-Surprisal)

dfs_semantic_surprisal(Prefix,W,MS,S) :-
        append(Prefix,[W],PrefixW),
        dfs_prefix_continuations(Prefix,Cs),
        dfs_prefix_continuations(PrefixW,CsW),
        findall(P, member((_,P),Cs),  Ps),
        findall(PW,member((_,PW),CsW),PsW),
        disjoin(Ps, Disj),
        disjoin(PsW,DisjW),
        dfs_surprisal(DisjW,Disj,MS,S).

% dfs_semantic_entropy(+Prefix,+ModelSet,-Entropy)

dfs_semantic_entropy(Prefix,MS,H) :-
        dfs_prefix_continuations(Prefix,Cs),
        findall(P,member((_,P),Cs),Ps),
        disjoin(Ps,Disj),
        dfs_entropy(Disj,MS,H).

% dfs_semantic_delta_entropy(+Prefix,+Word,+ModelSet,-DeltaEntropy)

dfs_semantic_delta_entropy(Prefix,W,MS,DH) :-
        append(Prefix,[W],PrefixW),
        dfs_semantic_entropy(Prefix, MS,H),
        dfs_semantic_entropy(PrefixW,MS,HW),
        DH is H - HW.

%%%%%%%%%%%%%%%$$$$$$$$$$%%%%%%%%%%%%%
%%%% even more experimental stuff %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% dfs_fapply_surprisal(+Formula0,+Formula1,+ModelSet|+ModelMatrix,-Surprisal)

dfs_fapply_surprisal(F0,F1,[(Um,Vm)|MS],S) :-
        !, dfs_models_to_matrix([(Um,Vm)|MS],MM),
        dfs_fapply_surprisal(F0,F1,MM,S).
dfs_fapply_surprisal(F0,F1,MM,S) :-
        dfs_function_vector(F0,MM,V0),
        dfs_fapply(F0,F1,F2),
        dfs_function_vector(F2,MM,V2),
        dfs_surprisal(V2,V0,S).

% dfs_fapply_surprisal(+Formula,+ModelSet|+ModelMatrix,-Surprisal)

dfs_fapply_entropy(F,[(Um,Vm)|MS],H) :-
        !, dfs_models_to_matrix([(Um,Vm)|MS],MM),
        dfs_fapply_entropy(F,MM,H).
dfs_fapply_entropy(F,MM,H) :-
        dfs_function_vector(F,MM,V),
        dfs_entropy(V,H).

% dfs_fapply_delta_entropy(+Formula0,+Formula1,+ModelSet|+ModelMatrix,-DeltaEntropy)

dfs_fapply_delta_entropy(F0,F1,[(Um,Vm)|MS],DH) :-
        !, dfs_models_to_matrix([(Um,Vm)|MS],MM),
        dfs_fapply_delta_entropy(F0,F1,MM,DH).
dfs_fapply_delta_entropy(F0,F1,MM,DH) :-
        dfs_function_vector(F0,MM,V0),
        dfs_fapply(F0,F1,F2),
        dfs_function_vector(F2,MM,V2),
        dfs_delta_entropy(V0,V2,DH).
