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
                dfs_models/1,
                dfs_pprint_model/1,
                dfs_pprint_model_matrix/1,
                dfs_pprint_fapply_deriv/1
        ]).

:- reexport(dfs_interpretation).
:- reexport(dfs_io).
:- reexport(dfs_properties).
:- reexport(dfs_probabilities).
:- reexport(dfs_type_theory).
:- reexport(dfs_sampling).
:- reexport(dfs_vector_space).

:- use_module(library(clpfd),[transpose/2]).

% models(-ModelSet)

dfs_models(MS) :-
        findall(M,user:model(M),MS).

% dfs_pprint_model(+Model)

dfs_pprint_model((Um,Vm)) :-
        format('\n%%%% Um = { '),
        pprint_atoms(Um),
        format(' }\n'),
        format('%%%%\n'),
        foreach(member(C=E,Vm),format('%%%% Vm ( ~a ) = ~a\n',[C,E])),
        format('%%%%\n'),
        pprint_vm(Vm),
        format('\n').

pprint_vm([]).
pprint_vm([P|Ps]) :-
        P =.. [Pred|[Args]],
        Pred \= (=), !,
        format('%%%% Vm ( ~a ) = { ',[Pred]),
        pprint_atoms(Args),
        format(' }\n'),
        pprint_vm(Ps).
pprint_vm([_|Ps]) :-
        pprint_vm(Ps).

pprint_atoms([]).
pprint_atoms([A|As]) :-
        (  atom(A)
        -> format('~a',[A]),
           ( As \= [] -> format(', ') ; true )
        ;  format('< '),
           pprint_atoms(A),
           format(' >'),
           ( As \= [] -> format(', ') ; true ) ),
        pprint_atoms(As).

% dfs_pprint_model_matrix(+ModelMatrix)

dfs_pprint_model_matrix(MM) :-
        transpose(MM,TMM),
        format('\n'),
        pprint_model_matrix_(TMM),
        format('\n').

pprint_model_matrix_([]).
pprint_model_matrix_([DV|DVs]) :-
        memberchk((P,_),DV),
        format('%%%% '),
        pprint_dfs_vector(DV),
        format(' ~w\n',[P]),
        pprint_model_matrix_(DVs).

pprint_dfs_vector([]).
pprint_dfs_vector([(_,S)|Ts]) :-
        format('~0f',[S]),
        ( Ts \= [] -> format('') ; true ),
        pprint_dfs_vector(Ts).

% dfs_pprint_fapply(Tuples)

dfs_pprint_fapply_deriv(Ts) :-
        format('\n'),
        dfs_pprint_fapply_deriv_(Ts),
        format('\n').

dfs_pprint_fapply_deriv_([]) :- !.
dfs_pprint_fapply_deriv_([(F,V)|Ts]) :-
        format('%%%% '),
        foreach(member(U,V),format('~2f ',[U])),
        format('~w\n',[F]),
        dfs_pprint_fapply_deriv_(Ts).
