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

:- module(dfs_sentences,
        [
                op(900,fx, @~),         %% sentence

                dfs_sentences/1,
                dfs_words/1,
                dfs_word_vectors/2,
                dfs_map_words_onto_semantics/4
        ]).

%% sentence(?Semantics,?Sentence,?Rest)
%
%  Note: Assumes @~/3 and sentence/3 to be top-level DCG rules.

sentence(P,S,R) :-
        current_predicate((@~)/3),
        @~(P,S,R).
sentence(P,S,R) :-
        current_predicate(user:sentence/3),
        user:sentence(P,S,R).

% dfs_sentences(-SenSemTuples)

dfs_sentences(SPMs) :-
        findall((S,P),sentence(P,S,[]),SPMs).

% dfs_words(-Words)

dfs_words(Ws) :-
        setof(W,P^S^R^(sentence(P,S,[]),select(W,S,R)),Ws).

% dfs_word_vectors(+Words,-WordVectors)

dfs_word_vectors(Ws,WVs) :-
       length(Ws,L),
       dfs_word_vectors_(Ws,L,1,WVs).

dfs_word_vectors_([],_,_,[]).
dfs_word_vectors_([W|Ws],L,I,[(W,V)|WVs]) :-
        localist_vector(L,I,V),
        I0 is I + 1,
        dfs_word_vectors_(Ws,L,I0,WVs).

% localist_vector(+NDims,+HotBit,-Vector)

localist_vector(N,HB,V) :-
        distributed_vector(N,[HB],V).

% localist_vector(+NDims,+HotBitSet,-Vector)

distributed_vector(N,HBs,V) :-
        N0 is N + 1,
        distributed_vector_(N0,HBs,1,V).

distributed_vector_(N,_,N,[]) :- !.
distributed_vector_(N,HBs,I,[1|Us]) :-
        memberchk(I,HBs), !,
        I0 is I + 1,
        distributed_vector_(N,HBs,I0,Us).
distributed_vector_(N,HBs,I,[0|Us]) :-
        I0 is I + 1,
        distributed_vector_(N,HBs,I0,Us).

%% dfs_map_words_onto_semantics((+Sen,+Sem),+ModelSet,+WordVecs,
%  -WordsSemMapping)

dfs_map_words_onto_semantics((S,P),Ms,WVs,SPM) :-
        dfs_vector(P,Ms,PV),
        dfs_map_words_onto_semantics_(S,WVs,PV,SPM).

dfs_map_words_onto_semantics_([],_,_,[]).
dfs_map_words_onto_semantics_([W|Ws],WVs,PV,[(W,WV,PV)|WPMs]) :-
        memberchk((W,WV),WVs),
        dfs_map_words_onto_semantics_(Ws,WVs,PV,WPMs).
