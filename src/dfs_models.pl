/*
 * dfs_models.pl
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

:- module(dfs_models,
        [
                dfs_models/1,
                dfs_assert_model/1,
                dfs_assert_models/1,
                dfs_retract_models/0,
                dfs_induce_model/2,
                dfs_induce_models/2,
                dfs_deduce_observation/2,
                dfs_deduce_observations/2
        ]).

:- use_module(dfs_vector_space).

:- dynamic user:model/1.
:- public  user:model/1.

/** <module> Models

Model assertion and retraction, as well as model induction and deduction.
*/

%!      dfs_models(-ModelSet) is det

dfs_models(MS) :-
        findall(M,user:model(M),MS).

%!      dfs_assert_model(+Model) is det.

dfs_assert_model(M) :-
        assert(user:model(M)).

%!      dfs_assert_models(+ModelSet) is det.

dfs_assert_models([]).
dfs_assert_models([M|Ms]) :-
        dfs_assert_model(M),
        dfs_assert_models(Ms).

%!      dfs_retract_models is det.

dfs_retract_models :-
        retractall(user:model(_)).

                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% induction/deduction %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_induce_model(+Observation,-Model) is det.
%
%       Instantiates a Model from a list of co-occuring atomic propositions
%       denoting an Observation.

dfs_induce_model(O,M) :-
        dfs_induce_model_(O,OV),
        dfs_vector_to_model(OV,M).

dfs_induce_model_([],[]).
dfs_induce_model_([AP|APs],[(AP,1)|APV]) :-
        dfs_induce_model_(APs,APV).

%!      dfs_induce_models(+Obervations,-ModelSet) is det.
%
%       @see dfs_induce_model/2.

dfs_induce_models([],[]).
dfs_induce_models([O|Os],[M|Ms]) :-
        dfs_induce_model(O,M),
        dfs_induce_models(Os,Ms).

%!      dfs_deduce_observation(+Model,-Observation) is det.
%
%       Maps a Model into a list of co-occuring atomic propositions denoting
%       an Observation.

dfs_deduce_observation(M,OV) :-
        dfs_model_to_vector(M,V),
        dfs_deduce_observation_(V,OV).

dfs_deduce_observation_([],[]).
dfs_deduce_observation_([(AP,1)|APV],[AP|APs]) :-
        !, dfs_deduce_observation_(APV,APs).
dfs_deduce_observation_([(_,0)|APV],APs) :-
        dfs_deduce_observation_(APV,APs).

%!      dfs_deduce_observations(+ModelSet,-Observations) is det.
%
%       @see dfs_deduce_observations/2.

dfs_deduce_observations([],[]).
dfs_deduce_observations([M|Ms],[O|Os]) :-
        dfs_deduce_observation(M,O),
        dfs_deduce_observations(Ms,Os).
