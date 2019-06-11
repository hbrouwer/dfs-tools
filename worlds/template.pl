/*
 * Copyright 2019 Noortje Venhuizen <njvenhuizen@gmail.com>
 *     and Harm Brouwer <me@hbrouwer.eu>
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

% Define path to DFS tools
:- use_module('../src/dfs_main.pl').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Constants and Predicates %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Define constants using 'constant' or '@+'
constant('c').
% @+ 'c'.

% Define n-place predicates over constants using 'property' or '@*'
property(pred('c')).
% @* pred('c').

%%%%%%%%%%%%%%%%%%%%%
%%%% Constraints %%%%
%%%%%%%%%%%%%%%%%%%%%

% Define hard constraints as FOL formulas within 'constraint' or '@#'
constraint(forall(x,pred(x))).
% @# forall(x,pred(x)).

% Define (conditional) probability for propositions, given a FOL constraint
% using 'probability' or '<-'.
probability(_,top,0.5).
% 0.5 <- (_ | top).

%%%%%%%%%%%%%%%%%%%
%%%% Sentences %%%%
%%%%%%%%%%%%%%%%%%%

% Define sentences as tuples consisting of a set of words and a FOL formula
% representing its semantics using 'sentence' or '@~'
sentence((['word'],pred('c'))).
% @~ (['word'],pred('c')).
