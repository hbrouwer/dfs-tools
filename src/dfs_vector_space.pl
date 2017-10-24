/*
 * dfs_vector_space.pl
 *
 * Copyright 2017 Harm Brouwer <me@hbrouwer.eu>
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

:- module(dfs_vector_space,
        [
                op(900,xfx,@>#), (@>#)/2,       %% models to vector space
                op(900,xfx,#>@), (#>@)/2,       %% vector space to models
                
                dfs_model_to_vector/2,
                dfs_models_to_matrix/2,
                dfs_vector_to_model/2,
                dfs_matrix_to_models/2,
                dfs_vector/3
        ]).

/** <module> Vector space

Conversion between sets of models and vector space.
*/

%!      atomic_propositions(+ModelSet,-AtomicProps) is det.
%
%       AtomicProps is the list of all atomic propositions in ModelSet.

atomic_propositions(MS,APs) :-
        atomic_propositions_(MS,[],APs).

atomic_propositions_([],APsAcc,APs) :- 
        list_to_ord_set(APsAcc,APs).
atomic_propositions_([(Um,Vm)|MS],APsAcc,APs) :-
        dfs_init_g((Um,Vm),G),
        dfs_term_instantiations((Um,Vm),G,TIs),
        findall(AP,
                ( member(Prop,Vm),
                  Prop =.. [Pred|[AsList]],
                  Pred \= (=),
                  member(As,AsList),
                  (  atom(As)
                  -> dfs_terms_to_entities(Ts,TIs,[As]) %% unary predicates
                  ;  dfs_terms_to_entities(Ts,TIs,As)   %% n-ary predicates
                  ),       
                  AP =.. [Pred|Ts],
                  \+ memberchk(AP,APsAcc) ),
                APs0),
        append(APs0,APsAcc,APsAcc0),
        atomic_propositions_(MS,APsAcc0,APs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% models to vector space %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_model_to_vector(+Model,-ModelVector) is det.
%
%       ModelVector is a set of tuples (AtomicProp,State) representing
%       the State of each atomic proposition AtomicProp in Model.

dfs_model_to_vector(M,MV) :-
        dfs_init_g(M,G),
        atomic_propositions([M],APs),
        dfs_model_to_vector_(M,APs,G,MV).

dfs_model_to_vector_(_,[],_,[]) :- !.
dfs_model_to_vector_(M,[AP|APs],G,[(AP,1)|Ts]) :-
        dfs_interpret(AP,M,G), !,
        !,
        dfs_model_to_vector_(M,APs,G,Ts).
dfs_model_to_vector_(M,[AP|APs],G,[(AP,0)|Ts]) :-
        dfs_model_to_vector_(M,APs,G,Ts).

%!      dfs_models_to_matrix(+ModelSet,-ModelMatrix) is det.
%
%       Convert a set of models into a vector space.
%
%       @see dfs_model_to_vector/2.

dfs_models_to_matrix(MS,MM) :-
        atomic_propositions(MS,APs),
        dfs_models_to_matrix_(MS,APs,MM).

dfs_models_to_matrix_([],_,[]).
dfs_models_to_matrix_([M|MS],APs,[MV|MVs]) :-
        dfs_init_g(M,G),
        dfs_model_to_vector_(M,APs,G,MV),
        dfs_models_to_matrix_(MS,APs,MVs).

%!      (+ModelSet @># -Matrix) is det.
%
%       @see dfs_models_to_matrix/2.

MS @># MM :- dfs_models_to_matrix(MS,MM).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% vector space to models %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      dfs_vector_to_model(+ModelVector,-Model)
%
%       Converts ModelVector, a set of tuples (AtomicProp,State) representing
%       the State of each atomic proposition AtomicProp, into a Model.

dfs_vector_to_model(MV,(Um,Vm)) :-
        constants_and_universe(MV,Cs,Um),
        ifunc_inst_constants(Cs,Um,VmCs),
        dfs_constant_instantiations((_,VmCs),CIs),
        ifunc_inst_properties(MV,CIs,VmPs),
        append(VmCs,VmPs,Vm).

%!      dfs_matrix_to_models(+ModelMatrix,-ModelSet) is det.
%
%       Convert a vector space into a set of models.
%
%       @see dfs_vector_to_model/2.

dfs_matrix_to_models([],[]).
dfs_matrix_to_models([MV|MVs],[M|MS]) :-
        dfs_vector_to_model(MV,M),
        dfs_matrix_to_models(MVs,MS).

%!      (+Matrix #>@ -ModelSet) is det.
%
%       @see dfs_matrix_to_models/2.

MM #>@ MS :- dfs_matrix_to_models(MM,MS).

%!      constants_and_universe(+ModelVector,-Constants,-Entities) is det.

constants_and_universe(MV,Cs,Um) :-
        %setof(C,AP^P^As^S^(member((AP,S),MV),AP =.. [P|As],member(C,As)),Cs),
        setof(C,AP^P^As^(member((AP,1),MV),AP =.. [P|As],member(C,As)),Cs),
        length(Cs,N),
        dfs_entities(N,Um).

%!      ifunc_inst_constants(+Constants,+Entities,-VmCs) is det.
%
%       Instantiate Constant=Entity declarations in an interpretation
%       function VmCs.

ifunc_inst_constants([],[],[]).
ifunc_inst_constants([C|Cs],[E|Es],[C=E|VmCs]) :-
        ifunc_inst_constants(Cs,Es,VmCs).

%!      ifunc_inst_properties(+ModelVector,+ConstInstantiations,-VmPs) is det.
%
%       Derive properties from the atomic propositions in ModelVector, and
%       instantiate them in an interpretation function VmPs, given the
%       constant instantiations in ConstInstantiations.

ifunc_inst_properties(MV,CIs,VmPs) :-
        setof(P,AP^As^(member((AP,1),MV),AP =.. [P|As]),Ps),
        ifunc_inst_properties_(Ps,MV,CIs,VmPs).

ifunc_inst_properties_([],_,_,[]).
ifunc_inst_properties_([P|Ps],MV,CIs,[Prop|VM]) :-
        ifunc_inst_property(P,MV,CIs,PIs),
        Prop =.. [P|[PIs]],
        ifunc_inst_properties_(Ps,MV,CIs,VM).

ifunc_inst_property(_,[],_,[]) :- !.
ifunc_inst_property(P,[(AP,1)|Ts],CIs,[Es|PIs]) :-
        AP =.. [P|[A|As]], !,
        (  As == []
        -> dfs_terms_to_entities([A|As],CIs,[Es])       %% unary predicates
        ;  dfs_terms_to_entities([A|As],CIs,Es) ),      %% n-ary predicates
        ifunc_inst_property(P,Ts,CIs,PIs).
ifunc_inst_property(P,[_|Ts],CIs,PIs) :-
        ifunc_inst_property(P,Ts,CIs,PIs).

%!      dfs_vector(+Formula,+ModelSet,-Vector) is det.
%!      dfs_vector(+Formula,+ModelMatrix,-Vector) is det.
%
%       A formula P is true in a model M iff [P]^M,g = 1 given an arbitrary
%       variable assignment g

dfs_vector(_,[],[]) :- !.
dfs_vector(P,[(Um,Vm)|MS],[U|Us]) :-
        !, dfs_init_g((Um,Vm),G),
        (  dfs_interpret(P,(Um,Vm),G)
        -> U = 1
        ;  U = 0 ),
        dfs_vector(P,MS,Us).
dfs_vector(P,MM,V) :-
        dfs_matrix_to_models(MM,MS),
        dfs_vector(P,MS,V).
