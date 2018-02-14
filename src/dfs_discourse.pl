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

:- module(dfs_discourse,
        [
                op(900,fx,@~~),         %% discourse

                dfs_map_discourse_onto_semantics/4,
                dfs_map_semantics_onto_discourse/4
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
%       SenSemTuples is a list of all sentence-semantics mappings represing
%       a discourse.       

discourse(SPMs) :-
        current_predicate((@~~)/1),
        @~~(SPMs).
discourse(SPMs) :-
        current_predicate(user:discourse/1),
        user:discourse(SPMs).

                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% discourse onto semantics %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

dfs_map_discourse_onto_semantics([],_,_,[]).
dfs_map_discourse_onto_semantics([SPM|SPMs],WVs,MS,[WPM|WPMs]) :-
        dfs_map_sentence_onto_semantics(SPM,WVs,MS,WPM),
        dfs_map_discourse_onto_semantics(SPMs,WVs,MS,WPMs).

                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% semantics onto discourse %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

dfs_map_semantics_onto_discourse([],_,_,[]).
dfs_map_semantics_onto_discourse([SPM|SPMs],WVs,MS,[PWM|PWMs]) :-
        dfs_map_semantics_onto_sentence(SPM,WVs,MS,PWM),
        dfs_map_semantics_onto_discourse(SPMs,WVs,MS,PWMs).