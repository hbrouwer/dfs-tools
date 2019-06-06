/*
 * Copyright 2017-2019 Harm Brouwer <me@hbrouwer.eu>
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
                op(900,fx,@~),          %% sentence

                dfs_sentences/1,
                dfs_words/1,
                dfs_localist_word_vectors/1,
                dfs_map_sentence_onto_semantics/4,
                dfs_sentence_semantics_mappings/3,
                dfs_map_semantics_onto_sentence/4,
                dfs_semantics_sentence_mappings/3,
                dfs_map_sentence_onto_sentence/4,
                dfs_sentence_sentence_mappings/3,
                dfs_prefix_continuations/2,
                dfs_prefix_frequency/2,
                dfs_sentence_frequency/2
        ]).

:- use_module(library(lists)).

:- use_module(dfs_vector_space).

:- public
        (@~)/1,
        user:sentence/1.

/** <module> Sentence generation

Generation of sentence-semantics (and vice versa) mappings.
*/

%!      sentence(-SenSemTuple)
%
%       SenSemTuple is a tuple (Sen,Sem) where Sem is the first-order logic
%       meaning representation of Sen.

sentence(SPM) :-
        current_predicate(user:(@~)/1),
        user:(@~(SPM)).
sentence(SPM) :-
        current_predicate(user:sentence/1),
        user:sentence(SPM).

%!      dfs_sentences(-SenSemTuples) is det.
%
%       SenSemTuples is a list of all sentence-semantics mappings generated.

dfs_sentences(SPMs) :-
        findall(SPM,sentence(SPM),SPMs).

%!      dfs_words(-Words) is det.
%
%       Words is the set of all lexical items generated.

dfs_words(Ws) :-
        setof(W,P^S^R^(sentence((S,P)),select(W,S,R)),Ws).

%!      dfs_localist_word_vectors(-WordVectors) is det.
%
%       WordVectors is a list of tuples (Word,Vector) where Vector is a
%       localist vector representation for each Word generated.

dfs_localist_word_vectors(WVs) :-
        dfs_words(Ws),
        length(Ws,L),
        dfs_localist_word_vectors_(Ws,L,1,WVs).

dfs_localist_word_vectors_([],_,_,[]).
dfs_localist_word_vectors_([W|Ws],L,I,[(W,V)|WVs]) :-
        localist_vector(L,I,V),
        I0 is I + 1,
        dfs_localist_word_vectors_(Ws,L,I0,WVs).

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

                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% sentences onto semantics %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_map_sentence_onto_semantics(+SenSemTuple,+WVecs,+ModelSet,
%!              -Mapping) is det.
%
%       Mapping is a quadruple (Sen,Sem,[SenVecs],[SemVec]), where 
%       SenVecs is a word-by-word vector-based mapping of a sentence (Sen)
%       onto single SemVec, a vector representation of its semantics (Sem).
%
%       Word vector representation (WVecs) are pre-specified (e.g., using 
%       dfs_localist_word_vectors/2), and a vector representation of the
%       sentence meaning, specified by the FOL formula Sem, is derived
%       from ModelSet.

dfs_map_sentence_onto_semantics((S,P),WVs,MS,(S,P,IVs,[TV])) :-
        dfs_vector(P,MS,TV),
        findall(IV,(member(W,S),memberchk((W,IV),WVs)),IVs).

%!      dfs_sentence_semantics_mappings(+WVecs,+ModelSet,-Mappings) is det.
%
%       Mappings is a list of quadruples (Sen,Sem,[SenVecs],[SemVec]).
%
%       @see dfs_maps_sentence_onto_semantics/4

dfs_sentence_semantics_mappings(WVs,MS,WPMs) :-
        dfs_sentences(SPMs),
        findall(WPM,
          ( member(SPM,SPMs),
            dfs_map_sentence_onto_semantics(SPM,WVs,MS,WPM) ),
          WPMs).

                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% semantics onto sentences %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_map_semantics_onto_sentence(+SenSemTuple,+WVecs,+ModelSet,
%!              -Mapping) is det.
%
%       Mapping is a quadruple (Sen,Sem,[SemVec],[SenVecs]), where SemVec
%       is a vector representation of a sentence semantics (Sem), and SenVecs
%       a word-by-word vector-based representation of the corresponding
%       sentence (Sen).
%
%       Word vector representation (WVecs) are pre-specified (e.g., using 
%       dfs_localist_word_vectors/2), and a vector representation of the
%       sentence meaning, specified by the FOL formula Sem, is derived
%       from ModelSet.

dfs_map_semantics_onto_sentence((S,P),WVs,MS,(S,P,[IV],TVs)) :-
        dfs_vector(P,MS,IV),
        findall(TV,(member(W,S),memberchk((W,TV),WVs)),TVs).

%!      dfs_semantics_sentence_mappings(+WVecs,+ModelSet,-Mappings) is det.
%
%       Mappings is a list of quadruples (Sen,Sem,[SemVec],[SenVecs]).
%
%       @see dfs_map_semantics_onto_sentence/4

dfs_semantics_sentence_mappings(WVs,MS,PWMs) :-
        dfs_sentences(SPMs),
        findall(PWM,
          ( member(SPM,SPMs),
            dfs_map_semantics_onto_sentence(SPM,WVs,MS,PWM) ),
          PWMs).

                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% sentences onto sentences %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_map_sentence_onto_sentence(+SenSemTuple,+InWVecs,+OutWVecs,
%!              -Mapping) is det.
%
%       Mapping is a quadruple (Sen,Sem,[InSenVecs],[OutSenVecs]), where
%       InSenVecs and OutSenVecs are word-by-word vector-based representations
%       of the corresponding sentence (Sen).

dfs_map_sentence_onto_sentence((S,P),WVs0,WVs1,(S,P,IVs,TVs)) :-
        findall(IV,(member(W,S),memberchk((W,IV),WVs0)),IVs),
        findall(TV,(member(W,S),memberchk((W,TV),WVs1)),TVs).

%!      dfs_sentence_sentence_mappings(+InWVecs,+OutWVecs,-Mappings) is det.
%
%       Mappings is a list of quadruples (Sen,Sem,[InSenVecs],[OutSenVecs]).
%
%       @see dfs_map_sentence_onto_sentence/4.

dfs_sentence_sentence_mappings(WVs0,WVs1,WWMs) :-
        dfs_sentences(SPMs),
        findall(WWM,
         ( member(SPM,SPMs),
           dfs_map_sentence_onto_sentence(SPM,WVs0,WVs1,WWM) ),
           WWMs).

                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% sentence/prefix frequencies %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_prefix_continuations(+Prefix,SemSenMappings) is det.
%
%       SemSenMappings is a list of all tuples (Sen,Sem), where sentence Sen
%       is a possible continuation of Prefix, and Sem its corresponding FOL
%       semantics.

dfs_prefix_continuations(Prefix,Cs) :-
        append(Prefix,_,Templ),
        findall((Templ,P),sentence((Templ,P)),Cs).

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
        findall(Sen,sentence((Sen,_)),Sens),
        length(Sens,F).
