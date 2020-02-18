/*
 * Copyright 2017-2020 Harm Brouwer <me@hbrouwer.eu>
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

 :- module(yap_terms,
        [
                read_term_from_atom/3
        ]).

%!      read_term_from_atom(+Atom,-Term,+Options) is det.
%
%       As in SWI-prolog: Use Atom as input to read_term/2 using the option 
%       variable_names and return the read term in Term and the variable
%       bindings in Bindings. Bindings is a list of Name = Var couples, thus
%       providing access to the actual variable names. See also read_term/2. 
%       If Atom has no valid syntax, a syntax_error exception is raised. New 
%       code should use read_term_from_atom/3.

read_term_from_atom(Atom,Term,_) :-
        atom_to_term(Atom,Term,_).
