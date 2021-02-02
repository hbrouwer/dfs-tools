/*
 * Copyright 2017-2021 Harm Brouwer <me@hbrouwer.eu>
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

:- module(dfs_io,
        [
                dfs_write_models/2,
                dfs_read_models/2,
                dfs_write_matrix/2,
                dfs_read_matrix/2,
                dfs_pprint_formula/1,
                dfs_pprint_model/1,
                dfs_pprint_propositions/1,
                dfs_pprint_matrix/1,
                dfs_pprint_constraints/0,
                dfs_pprint_entailments/1
        ]).

:- use_module(library(aggregate)).
:- use_module(library(clpfd)).
:- use_module(library(lists)).

:- use_module(dfs_discourse).
:- use_module(dfs_interpretation).
:- use_module(dfs_logic).
:- use_module(dfs_sentences).

% YAP compatibility
:- prolog_flag(version_data,V),
        V =.. [P|_],
        (  P == yap
        -> use_module('../yap/swi_predicates.pl'),
           use_module('../yap/yap_terms.pl')
        ;  use_module(library(readutil)) ).

/** <module> IO

Basic IO and pretty printing facilities.
*/

                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% reading/writing models %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_write_models(+ModelSet,+File) is det.
%
%       Writes ModelSet to File.

dfs_write_models(MS,File) :-
        open(File,write,Stream),
        dfs_write_models_(MS,Stream),
        close(Stream).

dfs_write_models_([],_).
dfs_write_models_([M|MS],Stream) :-
        format(Stream,'model((~w)).~n',M),
        dfs_write_models_(MS,Stream).

%!      dfs_read_models(+File,-ModelSet) is det.
%
%       Reads ModelSet from File.

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

                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% reading/writing matrices %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_write_matrix(+ModelMatrix,+File) is det.
%
%       Write ModelMatrix to File.

dfs_write_matrix([MV|MVs],File) :-
        open(File,write,Stream),
        findall(AP,member((AP,_),MV),APs),
        write_atomic_propositions(APs,Stream),
        write_model_matrix([MV|MVs],Stream),
        close(Stream).

%!      write_atomic_propositions(+AtomicProps,+Stream) is det.

write_atomic_propositions([AP],Stream) :-
        !, format(Stream,'~w~n',AP).
write_atomic_propositions([AP|APs],Stream) :-
        format(Stream,'~w ',AP),
        write_atomic_propositions(APs,Stream).

%!      write_model_matrix(+ModelMatrix,+Stream) is det.

write_model_matrix([],_).
write_model_matrix([MV|MVs],Stream) :-
        write_model_vector(MV,Stream),
        write_model_matrix(MVs,Stream).

%!      write_model_vector(+ModelVector,+Stream) is det.

write_model_vector([(_,U)],Stream) :-
        !, format(Stream,'~d~n',U).
write_model_vector([(_,U)|Us],Stream) :-
        format(Stream,'~d ',U),
        write_model_vector(Us,Stream).

%!      dfs_read_matrix(+File,-ModelMatrix) is det.
%
%       Read ModelMatrix from File.

dfs_read_matrix(File,MM) :-
        open(File,read,Stream),
        read_atomic_propositions(Stream,APs),
        read_model_matrix(Stream,APs,MM),
        close(Stream).

%!      read_atomic_propositions(+Stream,-AtomicProps) is det.

read_atomic_propositions(Stream,APs) :-
        read_line_to_codes(Stream,Line),
        atom_codes(Atom,Line),
        atomic_list_concat(Atoms,' ',Atom),
        findall(AP,(member(AP0,Atoms),read_term_from_atom(AP0,AP,[])),APs).

%!      read_model_matrix(+Stream,+AtomicProps,-ModelMatrix) is det.
%
%       Read ModelMatrix from File. Real valued units are converted into
%       binary units.

read_model_matrix(Stream,APs,MVs) :-
        read_line_to_codes(Stream,Line),
        (  Line \= end_of_file
        -> read_model_matrix(Stream,APs,MVsAcc),
           atom_codes(Atom,Line),
           atomic_list_concat(Atoms,' ',Atom),
           % findall(U,(member(U0,Atoms),read_term_from_atom(U0,U,[])),Us),
           findall(U,
                ( member(U0,Atoms),
                  read_term_from_atom(U0,U1,[]),
                  (  U1 > 0.0
                  -> U = 1
                  ;  U = 0 ) ),
                Us ),
           vector_to_model_vector(Us,APs,MV),
           MVs = [MV|MVsAcc]
        ;  MVs = [] ).

%!      vector_to_model_vector(+Vector,+AtomicProps,-ModelVector) is det.

vector_to_model_vector([],[],[]).
vector_to_model_vector([U|Us],[AP|APs],[(AP,U)|Ts]) :-
        vector_to_model_vector(Us,APs,Ts).

                %%%%%%%%%%%%%%%%%%%%%%%%%
                %%%% pretty printing %%%%
                %%%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_pprint_formula(+Formula) is det.
%
%       Pretty print a first-order logic formula.

dfs_pprint_formula(P) :-
        format_formula(P,F),
        format('~n~w~n~n',[F]).

%!      format_formula(+Formula,-FormattedFormula)
%
%       FormattedFormula is ASCII formatted version of a first-order logic 
%       Formula.
%
%       @tbd: format(atom(A),_,_) only works with SWI prolog. Need to adapt
%       to ISO prolog some day.

format_formula(T1=T2,A) :-
        !, % t1 = t2
        format(atom(A),'(~w=~w)',[T1,T2]).
format_formula(neg(P),A1) :-
        !, % !P,
        format_formula(P,A0),
        format(atom(A1),'!~a',[A0]).
format_formula(and(P,Q),A2) :-
        !, % P & Q,
        format_formula(P,A0),
        format_formula(Q,A1),
        format(atom(A2),'(~a & ~a)',[A0,A1]).
format_formula(or(P,Q),A2) :-
        !, % P | Q,
        format_formula(P,A0),
        format_formula(Q,A1),
        format(atom(A2),'(~a | ~a)',[A0,A1]).
format_formula(exor(P,Q),A2) :-
        !, % P (+) Q,
        format_formula(P,A0),
        format_formula(Q,A1),
        format(atom(A2),'(~a (+) ~a)',[A0,A1]).
format_formula(imp(P,Q),A2) :-
        !, % P -> Q,
        format_formula(P,A0),
        format_formula(Q,A1),
        format(atom(A2),'(~a -> ~a)',[A0,A1]).
format_formula(iff(P,Q),A2) :-
        !, % P <-> Q,
        format_formula(P,A0),
        format_formula(Q,A1),
        format(atom(A2),'(~a <-> ~a)',[A0,A1]).
format_formula(exists(X,P),A1) :-
        !, % ∃x P
        format_formula(P,A0),
        format(atom(A1),'∃~w (~a)',[X,A0]).
format_formula(forall(X,P),A1) :-
        !, % ∀x P
        format_formula(P,A0),
        format(atom(A1),'∀~w (~a)',[X,A0]).
format_formula(top,A) :-
        !, % ⊤
        format(atom(A),'⊤').
format_formula(bottom,A) :-
        !, % ⊥
        format(atom(A),'⊥').
format_formula(P,A) :-
        format(atom(A),'~w',P).

%!      dfs_pprint_model(+Model) is det.
%
%       Pretty print a model.

dfs_pprint_model((Um,Vm)) :-
        format('~n%%%% Um = { '),
        pprint_atoms(Um),
        format(' }~n'),
        format('%%%%~n'),
        foreach(member(C=E,Vm),format('%%%% Vm ( ~a ) = ~a~n',[C,E])),
        format('%%%%~n'),
        pprint_vm(Vm),
        format('~n').

pprint_vm([]).
pprint_vm([P|Ps]) :-
        P =.. [Pred|[Args]],
        Pred \= (=), !,
        format('%%%% Vm ( ~a ) = { ',[Pred]),
        pprint_atoms(Args),
        format(' }~n'),
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

%!      dfs_pprint_propositions(+Model) is det.
%
%       Pretty print the propositions of Model.

dfs_pprint_propositions((Um,Vm)) :-
        dfs_init_g((Um,Vm),G),
        dfs_term_instantiations((Um,Vm),G,TIs),
        format('~n'),
        dfs_pprint_propositions_(Vm,TIs),
        format('~n').

dfs_pprint_propositions_([],_).
dfs_pprint_propositions_([P|Ps],TIs) :-
        P =.. [Pred|[Args]],
        Pred \= (=), !,
        format('%%%% ~a: { ',[Pred]),
        pprint_terms(Args,TIs),
        format(' }~n'),
        dfs_pprint_propositions_(Ps,TIs).
dfs_pprint_propositions_([_|Ps],TIs) :-
        dfs_pprint_propositions_(Ps,TIs).

pprint_terms([],_).
pprint_terms([A|As],TIs) :-
        (  atom(A)
        -> dfs_terms_to_entities([T],TIs,[A]),
           format('~a',[T]),
           ( As \= [] -> format(', ') ; true )
        ;  format('< '),
           pprint_terms(A,TIs),
           format(' >'),
           ( As \= [] -> format(', ') ; true ) ),
        pprint_terms(As,TIs).

%!      dfs_pprint_matrix(+ModelMatrix) is det.
%
%       Pretty print ModelMatrix.

dfs_pprint_matrix(MM) :-
        transpose(MM,TMM),
        format('~n'),
        pprint_matrix_(TMM),
        format('~n').

pprint_matrix_([]).
pprint_matrix_([DV|DVs]) :-
        memberchk((P,_),DV),
        format('%%%% '),
        pprint_dfs_vector(DV),
        format(' ~w~n',[P]),
        pprint_matrix_(DVs).

pprint_dfs_vector([]).
pprint_dfs_vector([(_,S)|Ts]) :-
        format('~0f',[S]),
        ( Ts \= [] -> format('') ; true ),
        pprint_dfs_vector(Ts).

%!      dfs_pprint_constraints is det.
%
%       Pretty print model constraints.

dfs_pprint_constraints :-
        findall(C,dfs_sampling:constraint(C),Cs),
        format('~n'),
        dfs_pprint_constraints_(Cs,orig),
        format('~n').

dfs_pprint_constraints_([],_).
dfs_pprint_constraints_([C|Cs],orig) :-
        !, format_formula(C,F),
        format('%%%% ~a~n',[F]),
        format('%%%%~n'),
        dfs_sampling:optimize_constraint(C,Cs0),
        dfs_pprint_constraints_(Cs0,optm),
        ( Cs \= [] -> format('%%%%~n%%%%~n') ; true ),
        dfs_pprint_constraints_(Cs,orig).
dfs_pprint_constraints_([C|Cs],optm) :-
        dfs_complement(C,Cc),
        format_formula(C,F),
        format_formula(Cc,Fc),
        format('%%%% \t ~a~n',[F]),
        format('%%%% \t\t => ~a~n',[Fc]),
        ( Cs \= [] -> format('%%%%~n') ; true ),
        dfs_pprint_constraints_(Cs,optm).

%!      format_sentence(+Sentence,-FormattedSentence)
%
%       FormattedSentence is ASCII formatted version of Sentence.
%
%       @tbd: format(atom(A),_,_) only works with SWI prolog. Need to adapt
%       to ISO prolog some day.

format_sentence([W],A) :-
        !, format(atom(A),'~w',[W]).
format_sentence([W|Ws],A1) :-
        format_sentence(Ws,A0),
        format(atom(A1),'~w ~a',[W,A0]).

%!      dfs_pprint_entailments(+Entailments) is det.
%
%       Pretty print entailments.

dfs_pprint_entailments(ETs) :-
        format('%%%% < '),
        findall(Es,member((_,Es),ETs),ESs),
        pprint_entailments(ESs),
        format('>~n').

pprint_entailments([]).
pprint_entailments([ES|ESs]) :-
        format('{ '),
        pprint_entailments_(ES),
        format('}'),
        ( ESs \= [] -> format(', ') ; format(' ') ),
        pprint_entailments(ESs).

pprint_entailments_([]).
pprint_entailments_([E|Es]) :-
        format('~w',[E]),
        ( Es \= [] -> format(', ') ; format(' ') ), 
        pprint_entailments_(Es).
