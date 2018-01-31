/*
 * Copyright 2017-2018 Harm Brouwer <me@hbrouwer.eu>
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

:- module(coals,
        [
                coals_vectors/3
        ]).

:- use_module(library(debug)). % topic: coals
:- use_module(library(lists)).

:- use_module(dfs_sentences).

/** <module> COALS

Correlated Occurrence Analogue to Lexical Semantics (COALS) interface for a
Definite Clause Grammars (DCG).
*/

coals_vectors(WType,WSize,CVs) :-
        findall(Sen,dfs_sentences:sentence(_,Sen,[]),Sens), % no need for semantics ...
        dfs_words(Words),
        frequency_matrix(Words,Words,Sens,WType,WSize,CVs).

frequency_matrix([],_,_,_,_,[]).
frequency_matrix([RWord|RWords],CWords,Sens,WT,WS,[FV|FVs]) :-
        frequency_vector(CWords,RWord,Sens,WT,WS,FV),
        debug(coals,'~s: ~w',[RWord,FV]),
        frequency_matrix(RWords,CWords,Sens,WT,WS,FVs).

frequency_vector([],_,_,_,_,[]).
frequency_vector([CWord|CWords],RWord,Sens,WT,WS,[F|Fs]) :-
        windowed_frequency(Sens,RWord,CWord,WT,WS,0,F),
        frequency_vector(CWords,RWord,Sens,WT,WS,Fs).

windowed_frequency([],_,_,_,_,F,F).
windowed_frequency([Sen|Sens],RWord,CWord,WT,WS,FAcc,F) :-
        memberchk(RWord,Sen),
        memberchk(CWord,Sen), 
        !,
        findall(F0,
          ( append(LWindowRev,[RWord|RWindow],Sen),
            reverse(LWindowRev,LWindow),
            windowed_frequency_(LWindow,CWord,WT,WS,0,LF),
            windowed_frequency_(RWindow,CWord,WT,WS,0,RF),
            F0 is LF + RF ),
        F0s),
        sumlist(F0s,SF),
        FAcc0 is FAcc + SF,
        windowed_frequency(Sens,RWord,CWord,WT,WS,FAcc0,F).
windowed_frequency([_|Sens],RWord,CWord,WT,WS,FAcc,F) :-
        windowed_frequency(Sens,RWord,CWord,WT,WS,FAcc,F).

windowed_frequency_([],_,_,_,F,F) :- !.
windowed_frequency_(_, _,_,0,F,F) :- !.
windowed_frequency_([Word|Words],Word,WT,N,FAcc,F) :-
        WT = 'flat', !,
        FAcc0 is FAcc + 1,
        N0 is N - 1,
        windowed_frequency_(Words,Word,WT,N0,FAcc0,F).
windowed_frequency_([Word|Words],Word,WT,N,FAcc,F) :-
        WT = 'ramped', !,
        FAcc0 is FAcc + N,
        N0 is N - 1,
        windowed_frequency_(Words,Word,WT,N0,FAcc0,F).
windowed_frequency_([_|Words],Word,WT,N,FAcc,F) :-
        N0 is N - 1,
        windowed_frequency_(Words,Word,WT,N0,FAcc,F).
