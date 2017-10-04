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

:- module(dfs,
        [
                dfs_models/1
        ]).

:- reexport(dfs_interpretation).
:- reexport(dfs_io).
:- reexport(dfs_properties).
:- reexport(dfs_probabilities).
:- reexport(dfs_type_theory).
:- reexport(dfs_sampling).
:- reexport(dfs_vector_space).

% models(-ModelSet)

dfs_models(MS) :-
        findall(M,user:model(M),MS).
