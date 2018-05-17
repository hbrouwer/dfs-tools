/*  Part of SWI-Prolog

    Author:        R.A. O'Keefe, V.S. Costa, L. Damas, Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2011-2016, Universidade do Porto, University of Amsterdam,
                              VU University Amsterdam.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(swi_predicates,
          [ random_permutation/2,       % ?List, ?Permutation
            union/3,                    % +List1, +List2, -Union
            read_line_to_codes/2        % +Stream, -Codes (without trailing \n)
          ]).
:- use_module(library(lists)).          
    
%!  random_permutation(+List, -Permutation) is det.
%!  random_permutation(-List, +Permutation) is det.
%
%   Permutation is a random permutation of List. This is intended to
%   process the elements of List in   random order. The predicate is
%   symmetric.
%
%   @error instantiation_error, type_error(list, _).

random_permutation(List1, List2) :-
    is_list(List1),
    !,
    random_permutation_(List1, List2).
random_permutation(List1, List2) :-
    is_list(List2),
    !,
    random_permutation_(List2, List1).
% random_permutation(List1, List2) :-
%     partial_list(List1), partial_list(List2),
%     !,
%     instantiation_error(List1+List2).
% random_permutation(List1, List2) :-
%     must_be(list, List1),
%     must_be(list, List2).    

random_permutation_(List, RandomPermutation) :-
    key_random(List, Keyed),
    keysort(Keyed, Sorted),
    pairs_values(Sorted, RandomPermutation).

key_random([], []).
key_random([H|T0], [K-H|T]) :-
    random(K),
    key_random(T0, T).

%!  pairs_values(+Pairs, -Values) is det.
%
%   Remove the keys  from  a  list   of  Key-Value  pairs.  Same  as
%   pairs_keys_values(Pairs, _, Values)

pairs_values([], []).
pairs_values([_-V|T0], [V|T]) :-
    pairs_values(T0, T).

%!  union(+Set1, +Set2, -Set3) is det.
%
%   True if Set3 unifies with the union of  the lists Set1 and Set2. The
%   complexity of this predicate is |Set1|*|Set2|. A _set_ is defined to
%   be an unordered list  without   duplicates.  Elements are considered
%   duplicates if they can be unified.
%
%   @see ord_union/3

union([], L, L) :- !.
union([H|T], L, R) :-
    memberchk(H, L),
    !,
    union(T, L, R).
union([H|T], L, [H|R]) :-
    union(T, L, R).

%!  read_line_to_codes(+In:stream, -Line:codes) is det.
%
%   Read a line of input from  In   into  a list of character codes.
%   Trailing newline and  or  return   are  deleted.  Upon  reaching
%   end-of-file Line is unified to the atom =end_of_file=.

%pl_read_line_to_codes(Stream, Codes) :-
read_line_to_codes(Stream, Codes) :-
    get_code(Stream, C0),
    (   C0 == -1
    ->  Codes0 = end_of_file
    ;   read_1line_to_codes(C0, Stream, Codes0)
    ),
    Codes = Codes0.

read_1line_to_codes(-1, _, []) :- !.
read_1line_to_codes(10, _, []) :- !.
read_1line_to_codes(13, Stream, L) :-
    !,
    get_code(Stream, C2),
    read_1line_to_codes(C2, Stream, L).
read_1line_to_codes(C, Stream, [C|T]) :-
    get_code(Stream, C2),
    read_1line_to_codes(C2, Stream, T).
