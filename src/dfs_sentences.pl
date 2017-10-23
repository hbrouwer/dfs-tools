/*
 * dfs_sentences.pl
 *
 * Copyright 2017 Harm Brouwer <me@hbrouwer.eu>
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

:- module(dfs_sentences,
        [
                op(900,fx, @~),         %% sentence

                dfs_sentences/1,
                dfs_words/1,
                dfs_word_vectors/2,
                dfs_map_words_onto_semantics/4,
                dfs_prefix_continuations/2,
                dfs_prefix_frequency/2,
                dfs_sentence_frequency/2
        ]).

/** <module> Sentence generation

Generation of sentence-semantics mappings from a DCG.
*/

%!      sentence(-Semantics,?Sentence,?Rest) is nondet.
%
%       Semantics is the first-order logic meaning representation of Sentence
%       given Rest. Typically, Rest = [], such that Semantics represents the
%       meaning of an entire sentence.
%
%       Note: Assumes @~/3 and sentence/3 to be top-level DCG rules.

sentence(P,S,R) :-
        current_predicate((@~)/3),
        @~(P,S,R).
sentence(P,S,R) :-
        current_predicate(user:sentence/3),
        user:sentence(P,S,R).

%!      dfs_sentences(-SenSemTuples) is det.
%
%       SenSemTuples is a list of all sentence-semantics mappings generated
%       by the DCG.

dfs_sentences(SPMs) :-
        findall((S,P),sentence(P,S,[]),SPMs).

%!      dfs_words(-Words) is det.
%
%       Words is the set lexical items generated by the DCG.

dfs_words(Ws) :-
        setof(W,P^S^R^(sentence(P,S,[]),select(W,S,R)),Ws).

%!      dfs_word_vectors(+Words,-WordVectors) is det.
%
%       WordVectors is a list of tuples (Word,Vector) where Vector is a
%       localist vector representation for Word.

dfs_word_vectors(Ws,WVs) :-
       length(Ws,L),
       dfs_word_vectors_(Ws,L,1,WVs).

dfs_word_vectors_([],_,_,[]).
dfs_word_vectors_([W|Ws],L,I,[(W,V)|WVs]) :-
        localist_vector(L,I,V),
        I0 is I + 1,
        dfs_word_vectors_(Ws,L,I0,WVs).

%!      localist_vector(+NDims,+HotBit,-Vector) is det.
%
%       Vector is a localist vector of NDims dimensions with its HotBit
%       component set to 1, and all other components set to 0.

localist_vector(N,HB,V) :-
        distributed_vector(N,[HB],V).

%!      distributed_vector(+NDims,+HotBitSet,-Vector) is det.
%
%       Vector is a distributed vector of NDims dimensions with all
%       components in HotBitSet set to 1, and all others set to 0.

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

%!      dfs_map_words_onto_semantics((+Sen,+Sem),+WVecs,+ModelSet,
%               -SenSemMapping) is det.
%
%       Mapping is a word-by-word vector-based mapping of a sentence (Sen)
%       onto its semantics (Sem). Word vector representation (WVecs) are
%       pre-specified (@see dfs_word_vectors/2), and a vector representation
%       of the sentence meaning, specified by the FOL formula Sem, is derived
%       for ModelSet.       

dfs_map_words_onto_semantics((S,P),WVs,MS,SPM) :-
        dfs_vector(P,MS,PV),
        dfs_map_words_onto_semantics_(S,PV,WVs,SPM).

dfs_map_words_onto_semantics_([],_,_,[]).
dfs_map_words_onto_semantics_([W|Ws],PV,WVs,[(W,WV,PV)|WPMs]) :-
        memberchk((W,WV),WVs),
        dfs_map_words_onto_semantics_(Ws,PV,WVs,WPMs).

%!      dfs_prefix_continuations(+Prefix,SemSenMappings) is det.
%
%       SemSenMappings is a list of all tuples (Sen,Sem), where sentence Sen
%       is a possible continuation of Prefix, and Sem its corresponding FOL
%       semantics.

dfs_prefix_continuations(Prefix,Cs) :-
        append(Prefix,_,Templ),
        findall((Templ,P),sentence(P,Templ,[]),Cs).

%!      dfs_prefix_frequency(+Prefix,-Frequency) is det.
%
%       Frequency is the occurence frequency of sentence Prefix.

dfs_prefix_frequency(Prefix,F) :-
        dfs_prefix_continuations(Prefix,Cs),
        length(Cs,F).

%!      dfs_sentence_frequency(+Sentence,-Frequency) is det.
%
%       Frequency is is the occurrence frequency of Sentence.

dfs_sentence_frequency(Sen,F) :-
        findall(Sen,sentence(_,Sen,[]),Sens),
        length(Sens,F).
