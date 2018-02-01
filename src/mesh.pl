/*
 * Copyright 2017-2018 Harm Brouwer <me@hbrouwer.eu>
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

:- module(mesh,
        [
                mesh_write_set/2
        ]).

:- use_module(library(lists)).

%!      mesh_write_set(+Mappings,+File) is det.
%
%       Write all sentence-semantics or semantics-sentence Mappings to File
%       in MESH-readable format:
%
%       Item "sentence" num_words "semantics"
%       Input # # # Target # #
%       Input # # # Target # #
%       
%       [...]
%
%       where 'sentence' is a sentence, 'num_words' the number of words in
%       this sentence (and hence, the number of input and target events),
%       and 'semantics' its formatted FOL semantics. The '#'s are the integer
%       units of the input/target vectors.

mesh_write_set(Mappings,File) :-
        open(File,write,Stream),
        mesh_format_items(Mappings,Stream),
        close(Stream).

%!      mesh_format_items(+Mappings,+Stream) is det.
%
%       Write Mappings to Stream in MESH-readable format.

mesh_format_items([],_).
mesh_format_items([M|Ms],Stream) :-
        mesh_format_item(M,Stream),
        mesh_format_items(Ms,Stream).

%!      mesh_format_items(+Mapping,+Stream) is det.
%
%       Write Mapping to Stream in MESH-readable format.

mesh_format_item((S,P,IVs,TVs),Stream) :-
        format(Stream,'Item \"',[]),
        mesh_format_item_name(S,Stream),
        format(Stream,'\"',[]),
        length(IVs,NumInputs),
        length(TVs,NumTargets),
        NumEvents is max(NumInputs,NumTargets),
        format(Stream,' ~d',[NumEvents]),
        format_formula(P,FP),
        format(Stream,' \"~w\"~n',[FP]),
        mesh_format_events(IVs,TVs,Stream),
        format(Stream,'~n',[]).

%!      mesh_format_item_name(+Sentence,+Stream) is det.
%
%       Write Sentence to Stream in MESH-readable format.

mesh_format_item_name([W],Stream) :-
        !, format(Stream,'~w',[W]).
mesh_format_item_name([W|Ws],Stream) :-
        format(Stream,'~w ',[W]),
        mesh_format_item_name(Ws,Stream).

%!      mesh_format_events(+InputVecs,TargetVecs,+Stream) is det.
%
%       Write input-target vector pairs to Stream in MESH-readable format.

mesh_format_events([],_,_).
mesh_format_events([IV],[TV],Stream) :-
        !, mesh_format_event(IV,TV,Stream).
mesh_format_events([IV|IVs],[TV],Stream) :-
        !, mesh_format_event(IV,TV,Stream),
        mesh_format_events(IVs,[TV],Stream).
mesh_format_events([IV],[TV|TVs],Stream) :-
        !, mesh_format_event(IV,TV,Stream),
        mesh_format_events([IV],TVs,Stream).
mesh_format_events([IV|IVs],[TV|TVs],Stream) :-
        mesh_format_event(IV,TV,Stream),
        mesh_format_events(IVs,TVs,Stream).

%!      mesh_format_event(+InputVecs,TargetVecs,+Stream) is det.
%
%       Write input-target vector pair to Stream in MESH-readable format.

mesh_format_event(IV,TV,Stream) :-
        format(Stream,'Input ',[]),
        mesh_format_vector(IV,Stream),
        format(Stream,' Target ',[]),
        mesh_format_vector(TV,Stream),
        format(Stream,'\n',[]).

%!      mesh_format_vector(+Vector,+Stream) is det.
%
%       Write Vector to Stream in MESH-readable format.

mesh_format_vector([U],Stream) :-
        !, format(Stream,'~d',U).
mesh_format_vector([U|Us],Stream) :-
        format(Stream,'~d ',U),
        mesh_format_vector(Us,Stream).
