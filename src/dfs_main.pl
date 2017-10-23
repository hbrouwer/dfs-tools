/*
 * dfs_main.pl
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

:- module(dfs,
        [
                dfs_main/0,
                dfs_models/1,
                
                dfs_version_major/1,
                dfs_version_minor/1,
                dfs_version_patch/1
        ]).

/** <module> Distributional Formal Semantics

A library for Distributional Formal Semantics (DFS). 

@tbd Elaborate on DFS.
*/

:- reexport(dfs_information_theory).
:- reexport(dfs_interpretation).
:- reexport(dfs_io).
:- reexport(dfs_logic).
:- reexport(dfs_models).
:- reexport(dfs_properties).
:- reexport(dfs_probabilities).
:- reexport(dfs_type_theory).
:- reexport(dfs_sampling).
:- reexport(dfs_sentences).
:- reexport(dfs_vector_space).

:- initialization(dfs_main).

dfs_version_major(0).
dfs_version_minor(0).
dfs_version_patch(1).

dfs_main :-
        dfs_version_major(Vmaj),
        dfs_version_minor(Vmin),
        dfs_version_patch(Vpat),
        format('%%%% DFS Tools ~d.~d.~d | http://hbrouwer.github.io/dfs/\n\n',[Vmaj,Vmin,Vpat]).
