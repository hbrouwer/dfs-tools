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

:- module(dfs_io,
        [
                dfs_write_models/2,
                dfs_read_models/2,
                dfs_write_matrix/2,
                dfs_read_matrix/2
        ]).

% dfs_write_models(+ModelSet,+File)

dfs_write_models(MS,File) :-
        open(File,write,Stream),
        dfs_write_models_(MS,Stream),
        close(Stream).

dfs_write_models_([],_).
dfs_write_models_([M|MS],Stream) :-
        format(Stream,'model((~w)).\n',M),
        dfs_write_models_(MS,Stream).

% dfs_read_models(+File,-ModelSet)

dfs_read_models(File,MS) :-
        open(File,read,Stream),
        dfs_read_models_(Stream,MS),
        close(Stream).

dfs_read_models_(Stream,MS) :-
        read_line_to_codes(Stream,Line),
        (  Line \= end_of_file
        -> dfs_read_models_(Stream,MSAcc),
           atom_codes(Atom,Line),
           read_term_from_atom(Atom,Term,[]),
           Term =.. [model|[M]],
           MS = [M|MSAcc]
        ;  MS = [] ).

% dfs_write_matrix(+ModelMatrix,+File)

dfs_write_matrix([MV|MVs],File) :-
        open(File,write,Stream),
        findall(AP,member((AP,_),MV),APs),
        write_atomic_propositions(APs,Stream),
        write_model_matrix([MV|MVs],Stream),
        close(Stream).

% write_atomic_propositions(+AtomicProps,+Stream)

write_atomic_propositions([AP],Stream) :-
        !, format(Stream,'~w\n',AP).
write_atomic_propositions([AP|APs],Stream) :-
        format(Stream,'~w ',AP),
        write_atomic_propositions(APs,Stream).

% write_model_matrix(+ModelMatrix,+Stream)

write_model_matrix([],_).
write_model_matrix([MV|MVs],Stream) :-
        write_model_vector(MV,Stream),
        write_model_matrix(MVs,Stream).

% write_model_vector(+ModelVector,+Stream)

write_model_vector([(_,U)],Stream) :-
        !, format(Stream,'~d\n',U).
write_model_vector([(_,U)|Us],Stream) :-
        format(Stream,'~d ',U),
        write_model_vector(Us,Stream).

% dfs_read_matrix(+File,-ModelMatrix)

dfs_read_matrix(File,MM) :-
        open(File,read,Stream),
        read_atomic_propositions(Stream,APs),
        read_model_matrix(Stream,APs,MM),
        close(Stream).

% read_atomic_propositions(+Stream,-AtomicProps)

read_atomic_propositions(Stream,APs) :-
        read_line_to_codes(Stream,Line),
        atom_codes(Atom,Line),
        atomic_list_concat(Atoms,' ',Atom),
        findall(AP,(member(AP0,Atoms),read_term_from_atom(AP0,AP,[])),APs).

% read_model_matrix(+Stream,+AtomicProps,-ModelMatrix)

read_model_matrix(Stream,APs,MVs) :-
        read_line_to_codes(Stream,Line),
        (  Line \= end_of_file
        -> read_model_matrix(Stream,APs,MVsAcc),
           atom_codes(Atom,Line),
           atomic_list_concat(Atoms,' ',Atom),
           % findall(U,(member(U0,Atoms),read_term_from_atom(U0,U,[])),Us),
           %%%% read as binary vectors
           findall(U,
                ( member(U0,Atoms),
                  read_term_from_atom(U0,U1,[]),
                  (  U1 > 0.0
                  -> U = 1
                  ;  U = 0 ) ),
                Us ),
           %%%% 
           vector_to_model_vector(Us,APs,MV),
           MVs = [MV|MVsAcc]
        ;  MVs = [] ).

% vector_to_model_vector(+Vector,+AtomicProps,-ModelVector)

vector_to_model_vector([],[],[]).
vector_to_model_vector([U|Us],[AP|APs],[(AP,U)|Ts]) :-
        vector_to_model_vector(Us,APs,Ts).
