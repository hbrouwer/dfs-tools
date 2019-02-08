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

:- module(dfs_discourse,
        [
                op(900,fx,@~~),         %% discourse

                dfs_discourse/1,
                dfs_map_discourse_onto_semantics/4,
                dfs_discourse_semantics_mappings/3,
                dfs_map_semantics_onto_discourse/4,
                dfs_semantics_discourse_mappings/3
        ]).

:- use_module(library(lists)).

:- use_module(dfs_sentences).

:- public
        (@~~)/1,
        user:discourse/1.
        
/** <module> Discourse generation

Generation of discourse-semantics (and vice versa) mappings.
*/

%!      discourse(-SenSemTuples)
%
%       SenSemTuples is a list of all sentence-semantics mappings representing
%       a discourse.       

discourse(SPMs) :-
        current_predicate(user:(@~~)/1),
        user:(@~~(SPMs)).
discourse(SPMs) :-
        current_predicate(user:discourse/1),
        user:discourse(SPMs).

%!      dfs_discourse(SenSemTuples) is det.
%
%       SenSemTuples is a list of all discourse sentence-semantics mappings.

dfs_discourse(DPMs) :-
        findall(DPM,discourse(DPM),DPMs).

                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% discourse onto semantics %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_map_discourse_onto_semantics(+SenSemTuples,+WVecs,+ModelSet,
%               -Mappings) is det.
%
%       Mappings is a list of quadruples (Sen,Sem,[SenVecs],[SemVec]), where 
%       SenVecs is a word-by-word vector-based mapping of a sentence (Sen)
%       onto single SemVec, a vector representation of its semantics (Sem).
%
%       @see dfs_map_sentence_onto_semantics/4

dfs_map_discourse_onto_semantics([],_,_,[]).
dfs_map_discourse_onto_semantics([SPM|SPMs],WVs,MS,[WPM|WPMs]) :-
        dfs_map_sentence_onto_semantics(SPM,WVs,MS,WPM),
        dfs_map_discourse_onto_semantics(SPMs,WVs,MS,WPMs).

%!      dfs_discourse_semantics_mappings(+WVecs,+ModelSet,-Mappings) is det.
%
%       Mappings is a list of lists of (Sen,Sem,[SenVecs],[SemVec])
%       quadruples.
%
%       @see dfs_map_discourse_onto_semantics/4

dfs_discourse_semantics_mappings(WVs,MS,WPMs) :-
        dfs_discourse(DPMs),
        findall(WPM,
          ( member(DPM,DPMs),
            dfs_map_discourse_onto_semantics(DPM,WVs,MS,WPM) ),
          WPMs).
        
                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% semantics onto discourse %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_map_semantics_onto_discourse(+SenSemTuples,+WVecs,+ModelSet,
%               -Mappings) is det.
%
%       Mappings is a list of quadruples (Sen,Sem,[SemVec],[SenVecs]), where
%       SemVec is a vector representation of a sentence semantics (Sem), and
%       SenVecs a word-by-word vector-based representation of the
%       corresponding sentence (Sen).
%
%       @see dfs_map_semantics_onto_sentence/4

dfs_map_semantics_onto_discourse([],_,_,[]).
dfs_map_semantics_onto_discourse([SPM|SPMs],WVs,MS,[PWM|PWMs]) :-
        dfs_map_semantics_onto_sentence(SPM,WVs,MS,PWM),
        dfs_map_semantics_onto_discourse(SPMs,WVs,MS,PWMs).

%!      dfs_semantics_discourse_mappings(+WVecs,+ModelSet,-Mappings) is det.
%
%       Mappings is a list of lists of quadruples
%       (Sen,Sem,[SemVec],[SenVecs]).
%
%       @see dfs_map_semantics_onto_discourse/4

dfs_semantics_discourse_mappings(WVs,MS,PWMs) :-
        dfs_discourse(DPMs),
        findall(PWM,
          ( member(DPM,DPMs),
            dfs_map_semantics_onto_discourse(DPM,WVs,MS,PWM) ),
          PWMs).
