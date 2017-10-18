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

:- module(dfs_models,
        [
                dfs_models/1,
                dfs_assert_model/1,
                dfs_assert_models/1,
                dfs_retract_models/0,
                dfs_induce_model/2
        ]).

:- dynamic(user:model/1).

% dfs_models(-ModelSet)

dfs_models(MS) :-
        findall(M,user:model(M),MS).

% dfs_assert_model(+Model)

dfs_assert_model(M) :-
        assert(user:model(M)).

% dfs_assert_models(+ModelSet)

dfs_assert_models([]).
dfs_assert_models([M|Ms]) :-
        dfs_assert_model(M),
        dfs_assert_models(Ms).

% dfs_retract_models/0

dfs_retract_models :-
        retractall(user:model(_)).

%%%%%%%%%%%%%%%%%%%
%%%% induction %%%%
%%%%%%%%%%%%%%%%%%%

% dfs_induce_model(+TrueAtomicPropositions,-Model)

dfs_induce_model(TAPs,M) :-
        dfs_induce_model_(TAPs,TAPsV),
        dfs_vector_to_model(TAPsV,M).

dfs_induce_model_([],[]).
dfs_induce_model_([AP|APs],[(AP,1)|APV]) :-
        dfs_induce_model_(APs,APV).

% dfs_induce_models([+AtomicPropositions],-ModelSet)

% dfs_induce_models([],[]).
% dfs_induce_models([MD|MDs],[M|Ms]) :-
%         dfs_induce_model(MD,M),
%         dfs_induce_models(MDs,Ms).
