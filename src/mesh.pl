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
                mesh_write_set/2,
                mesh_write_atomic_prop_set/2
        ]).

:- use_module(library(lists)).

/** <module> MESH

Write MESH-readable sets.
*/

%!      mesh_write_set([+SentenceSemanticsMapping],+File) is det.
%!      mesh_write_set([+DiscourseSemanticsMapping],+File) is det.
%
%       Write all sentence-semantics, semantics-sentence, discourse-semantics,
%       or semantics-discourse Mappings to File in MESH-readable format.
%
%       Sentences format:
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
%
%       Discourse format:
%
%       Item "sentence1 #### sentence2" num_words "semantics1 #### semantics2"
%       Input # # # Target # #
%       Input # # # Target # #
%
%       [...]
%
%       where 'sentence1' and 'sentence2' are sentences of a discourse,
%       'num_words' the number of words of the discourse, and 'semantics1'
%       and 'semantics2' the (possibly) varying semantics for the two
%       sentences. The single '#'s are the integer units of the input/target
%       vectors, and the '####' string is a sentence divider.

mesh_write_set(Mappings,File) :-
        open(File,write,Stream),
        mesh_format_items(Mappings,Stream),
        close(Stream).

%!      mesh_format_items([+SentenceSemanticsMapping],+Stream) is det.
%!      mesh_format_items([+DiscourseSemanticsMapping],+Stream) is det.
%
%       Write Mappings to Stream in MESH-readable format.

mesh_format_items([],_).
mesh_format_items([M|Ms],Stream) :-
        mesh_format_item(M,Stream),
        mesh_format_items(Ms,Stream).

%!      mesh_format_item(+SentenceSemanticsMapping,+Stream) is det.
%!      mesh_format_item(+DiscourseSemanticsMapping,+Stream) is det.
%
%       Write Mapping to Stream in MESH-readable format, where Mapping is
%       either a single quadruple (Sen,Sem,[InputVecs],[TargetVecs])
%       representing a sentence, or a list of quadruples representing a
%       discourse.

mesh_format_item((S,P,IVs,TVs),Stream) :-
        format(Stream,'Item \"',[]),
        mesh_format_sentence_string(S,Stream),
        format(Stream,'\"',[]),
        length(S,NumEvents),
        format(Stream,' ~d',[NumEvents]),
        format(Stream,' \"',[]),
        mesh_format_sentence_formula(P,Stream),
        format(Stream,'\"~n',[]),
        mesh_format_sentence_events(IVs,TVs,Stream),
        format(Stream,'~n',[]).
mesh_format_item([M|Ms],Stream) :-
        mesh_linearize_item([M|Ms],(LS,LP,LIVs,LTVs)),
        format(Stream,'Item \"',[]),
        mesh_format_discourse_string(LS,Stream),
        format(Stream,'\"',[]),
        flatten(LS,FLS),
        length(FLS,NumEvents),
        format(Stream,' ~d',[NumEvents]),
        format(Stream,' \"',[]),
        mesh_format_discourse_formula(LP,Stream),
        format(Stream,'\"~n',[]),
        mesh_format_discourse_events(LIVs,LTVs,Stream),
        format(Stream,'~n',[]).

%!      mesh_linearize_items(+ListOfQuadruple,-QuadrupleOfLists) is det.
%
%       Converts a list of (Sen,Sem,[InputVecs],[TargetVecs]) quadruples,
%       into a quadruple of lists.

mesh_linearize_item([(S,P,IVs,TVs)],([S],[P],[IVs],[TVs])) :- !.
mesh_linearize_item([(S,P,IVs,TVs)|Ms0],([S|LS],[P|LP],[IVs|LIVs],[TVs|LTVs])) :-
        mesh_linearize_item(Ms0,(LS,LP,LIVs,LTVs)).

%!      mesh_format_sentence_string(+Sentence,+Stream) is det.
%
%       Write Sentence to Stream in MESH-readable format.

mesh_format_sentence_string(S,Stream) :-
        dfs_io:format_sentence(S,FS),
        format(Stream,'~w',[FS]).

%!      mesh_format_discourse_string(+Discourse,+Stream) is det.
%
%       Write Discourse to Stream in MESH-readable format. This separates the
%       individual sentences of Discourse with a '####' divider.

mesh_format_discourse_string([DS],Stream) :-
        !, mesh_format_sentence_string(DS,Stream).
mesh_format_discourse_string([DS|DSs],Stream) :-
        mesh_format_sentence_string(DS,Stream),
        format(Stream,' #### ',[]),
        mesh_format_discourse_string(DSs,Stream).

%!      mesh_format_sentence_string(+SentenceFormula,+Stream) is det.
%
%       Write SentenceFormula to Stream in MESH-readable format.

mesh_format_sentence_formula(P,Stream) :-
        dfs_io:format_formula(P,FP),
        format(Stream,'~w',[FP]).

%!      mesh_format_discourse_formula(+DiscourseFormula,+Stream) is det.
%
%       Write DiscourseFormula to Stream in MESH-readable format. This
%       separates the formulas corresponding to the individual sentences
%       of a discourse with a '####' divider.

mesh_format_discourse_formula([P],Stream) :-
        !, dfs_io:format_formula(P,FP),
        format(Stream,'~w',[FP]).
mesh_format_discourse_formula([P|Ps],Stream) :-
        dfs_io:format_formula(P,FP),
        format(Stream,'~w #### ',[FP]),
        mesh_format_discourse_formula(Ps,Stream).

%!      mesh_format_sentence_events(+InputVecs,TargetVecs,+Stream) is det.
%
%       Write the input-target vector pairs of a sentence to Stream in
%       MESH-readable format.

mesh_format_sentence_events([],_,_).
mesh_format_sentence_events([IV],[TV],Stream) :-
        !, mesh_format_event(IV,TV,Stream).
mesh_format_sentence_events([IV|IVs],[TV],Stream) :-
        !, mesh_format_event(IV,TV,Stream),
        mesh_format_sentence_events(IVs,[TV],Stream).
mesh_format_sentence_events([IV],[TV|TVs],Stream) :-
        !, mesh_format_event(IV,TV,Stream),
        mesh_format_sentence_events([IV],TVs,Stream).
mesh_format_sentence_events([IV|IVs],[TV|TVs],Stream) :-
        mesh_format_event(IV,TV,Stream),
        mesh_format_sentence_events(IVs,TVs,Stream).

%!      mesh_format_discourse_events([+InputVecs],[+TargetVecs],+Stream)
%!              is det.
%
%       Write the input-target vector pairs of each sentence of a discourse
%       to Stream in MESH-readable format.

mesh_format_discourse_events([],[],_).
mesh_format_discourse_events([IVs|DIVs],[TVs|DTVs],Stream) :-
        mesh_format_sentence_events(IVs,TVs,Stream),
        mesh_format_discourse_events(DIVs,DTVs,Stream).

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

%!      mesh_write_atomic_prop_set(+ModelSet,+File) is det.
%
%       Write a MESH-readable set of atomic propositions:
%
%       Item "atomic_prop1" 1 "atomic_prop1"
%       Input 0 0 0 Target 1 0 1 0 0
%
%       For each atomic proposition, the input vector is the zero vector with
%       number of dimensions equal to the number of words produced by
%       dfs_words/1, and the target vector is the vector encoding the atomic
%       proposition. 

mesh_write_atomic_prop_set(MS,File) :-
        dfs_words(Ws),
        length(Ws,NWs),
        dfs_sentences:distributed_vector(NWs,[],IV),
        dfs_vector_space:atomic_propositions(MS,APs),
        open(File,write,Stream),
        mesh_write_atomic_prop_set_(APs,MS,IV,Stream),
        close(Stream).

mesh_write_atomic_prop_set_([],_,_,_).
mesh_write_atomic_prop_set_([AP|APs],Ms,IV,Stream) :-
        format(Stream,'Item \"',[]),
        mesh_format_sentence_formula(AP,Stream),
        format(Stream,'\" 1 \"',[]),
        mesh_format_sentence_formula(AP,Stream),
        format(Stream,'\"~n',[]),
        dfs_vector(AP,Ms,TV),
        mesh_format_sentence_events([IV],[TV],Stream),
        format(Stream,'~n',[]),
        mesh_write_atomic_prop_set_(APs,Ms,IV,Stream).
