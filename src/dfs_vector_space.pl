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

:- module(dfs_vector_space,
        [
                dfs_derive_model_vector/2,
                dfs_derive_model_matrix/2,
                dfs_derive_model/2,
                dfs_derive_model_set/2,
                dfs_vector/3
        ]).

:- use_module(dfs_interpretation).

% constants(+Model|+ModelVector,-Constants)

constants((_,Vm),Cs) :-
        !, findall(C,member(C=_,Vm),Cs).
constants([(AP,S)|Ts],Cs) :-
        findall(Cs0,
                ( member((AP0,_),[(AP,S)|Ts]),
                  AP0 =.. [_|Cs0] ),
                Cs1),
        flatten(Cs1,Cs2),
        list_to_ord_set(Cs2,Cs).

% predicates(+Model|+ModelVector,-Predicates)

predicates((_,Vm),Ps) :-
        !, findall((Pred,N),
                ( member(Prop,Vm),
                  Prop =.. [Pred|[[Arg|_]]],
                  Pred \= (=),
                  (  atom(Arg)
                  -> N = 1
                  ;  length(Arg,N) ) ),
                Ps).
predicates([(AP,S)|Ts],Ps) :-
        findall((Pred,N),
                ( member((AP0,_),[(AP,S)|Ts]),
                  AP0 =.. [Pred|Cs],
                  length(Cs,N) ),
                Ps0),
        list_to_ord_set(Ps0,Ps).

% atomic_propositions(+Model|+ModelSet|+ModelVec|+ModelMtx,-AtomicProps)

atomic_propositions((Um,Vm),APs) :-
        !, atomic_propositions_([(Um,Vm)],[],APs).
atomic_propositions([(Um,Vm)|MS],APs) :-
        is_list(Um),
        !, atomic_propositions_([(Um,Vm)|MS],[],APs).
atomic_propositions([(AP,_)|MV],APs) :-
        !, findall(AP0,member((AP0,_),[(AP,_)|MV]),APs).
atomic_propositions([MV|_],APs) :-
        atomic_propositions(MV,APs).

atomic_propositions_([],APs,APs) :- !.
atomic_propositions_([M|MS],APsAcc,APs) :-
        predicates(M,Ps),
        constants(M,Cs),
        dfs_init_g(M,G),
        findall(AP,
                ( member((P,N),Ps),
                  arguments(N,Cs,As),
                  AP =.. [P|As],
                  dfs_interpret(AP,M,G) ),
                APs0),
        append(APs0,APsAcc,APsAcc0),
        list_to_ord_set(APsAcc0,APsAcc1),
        atomic_propositions_(MS,APsAcc1,APs).

% arguments(+N,+Constants,-Args)

arguments(0,_,[]) :- !.
arguments(N,Cs,[Arg|Args]) :-
        select(Arg,Cs,_),
        N0 is N - 1,
        arguments(N0,Cs,Args).

% dfs_derive_model_vector(+Model,-ModelVector)

dfs_derive_model_vector(M,MV) :-
        dfs_init_g(M,G),
        atomic_propositions(M,APs),
        dfs_derive_model_vector_(M,APs,G,MV).

dfs_derive_model_vector_(_,[],_,[]) :- !.
dfs_derive_model_vector_(M,[AP|APs],G,[(AP,1)|Ts]) :-
        dfs_interpret(AP,M,G), !,
        dfs_derive_model_vector_(M,APs,G,Ts).
dfs_derive_model_vector_(M,[AP|APs],G,[(AP,0)|Ts]) :-
        dfs_derive_model_vector_(M,APs,G,Ts).

% dfs_derive_model_matrix(+ModelSet,-ModelMatrix)

dfs_derive_model_matrix(MS,MM) :-
        atomic_propositions(MS,APs),
        dfs_derive_model_matrix_(MS,APs,MM).

dfs_derive_model_matrix_([],_,[]) :- !.
dfs_derive_model_matrix_([M|MS],APs,[MV|MVs]) :-
        dfs_init_g(M,G),
        dfs_derive_model_vector_(M,APs,G,MV),
        dfs_derive_model_matrix_(MS,APs,MVs).

% dfs_derive_model(+ModelVector,-Model)

dfs_derive_model(MV,(Um,Vm)) :-
        constants(MV,Cs),
        length(Cs,N),
        dfs_entities(N,Um),
        derive_constants(Cs,Um,Vm0),
        dfs_constant_instantiations((_,Vm0),CIs),
        predicates(MV,Ps),
        derive_properties(Ps,MV,CIs,Vm1),
        append(Vm0,Vm1,Vm).

% dfs_derive_model_set(+ModelMatrix,-ModelSet)

dfs_derive_model_set([],[]) :- !.
dfs_derive_model_set([MV|MVs],[M|MS]) :-
        dfs_derive_model(MV,M),
        dfs_derive_model_set(MVs,MS).

% derive_constants(+Constants,+Entities,-Vm)

derive_constants([],[],[]) :- !.
derive_constants([C|Cs],[E|Es],[C=E|Vm]) :-
        derive_constants(Cs,Es,Vm).

% derive_properties(+Predicates,+ModelVector,+ConstInsts,-Vm)

derive_properties([],_,_,[]) :- !.
derive_properties([(Pred,N)|Ps],MV,CIs,[Prop|VM]) :-
        derive_property_instantiations((Pred,N),MV,CIs,PIs),
        PIs \= [], !,
        Prop =.. [Pred|[PIs]],
        derive_properties(Ps,MV,CIs,VM).
derive_properties([_|Ps],MV,CIs,VM) :-
        derive_properties(Ps,MV,CIs,VM).

% derive_property_instantions(+Pred,+ModelVector,+ConstInsts,-Vm)

derive_property_instantiations(_,[],_,[]) :- !.
derive_property_instantiations((Pred,N),[(AP,1)|Ts],CIs,[Es|PIs]) :-
        AP =.. [Pred|Args], !,
        (  N == 1
        -> dfs_terms_to_entities(Args,CIs,[Es])  %% unary predicates
        ;  dfs_terms_to_entities(Args,CIs,Es) ), %% n-ary predicates
        derive_property_instantiations((Pred,N),Ts,CIs,PIs).
derive_property_instantiations((Pred,N),[_|Ts],CIs,PIs) :-
        derive_property_instantiations((Pred,N),Ts,CIs,PIs).

%% dfs_vector(+Formula,+ModelSet|+ModelMatrix,-Vector)
%
%  A formula P is true in a model M iff:
%
%       [P]^M,g = 1 given an arbitrary variable assignment g

dfs_vector(_,[],[]) :- !.
dfs_vector(P,[(Um,Vm)|MS],[U|Us]) :-
        !, dfs_init_g((Um,Vm),G),
        (  dfs_interpret(P,(Um,Vm),G)
        -> U = 1
        ;  U = 0 ),
        dfs_vector(P,MS,Us).
dfs_vector(P,MM,V) :-
        dfs_derive_model_set(MM,MS),
        dfs_vector(P,MS,V).
