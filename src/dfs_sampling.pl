/*
 * dfs_sampling.pl
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

:- module(dfs_sampling,
        [
                op(900,fx, @+),         %% constant
                op(900,fx, @*),         %% property
                op(900,fx, @#),         %% constraint
                op(900,xfx,<-),         %% probability

                dfs_sample_models/2,
                dfs_sample_model/1
        ]).

:- use_module(library(debug)). % topic: dfs_sampling

/** <module> Model sampling

Sample models from a world specification.

@tbd Elaborate on world specifications.
*/

%!      constant(-Constant) is nondet.

constant(C) :-
        current_predicate((@+)/1),
        @+ C.
constant(C) :-
        current_predicate(user:constant/1),
        user:constant(C).

%!      property(-Property) is nondet.

property(P) :- 
        current_predicate((@*)/1),
        @* P.
property(P) :- 
        current_predicate(user:property/1),
        user:property(P).

%!      constraint(-Constraint) is nondet.

constraint(C) :-
        current_predicate((@#)/1),
        @# C.
constraint(C) :- 
        current_predicate(user:constraint/1),
        user:constraint(C).

%!      probability(+Proposition,-Constraint,-Pr) is nondet.

probability(P,C,Pr) :- 
        current_predicate((<-)/2),
        Pr <- (P|C).
probability(P,C,Pr) :-
        current_predicate(user:probability/3),
        user:probability(P,C,Pr).

%!      dfs_sample_models(+NumModels,-ModelSet) is det.
%
%       ModelSet is a set of NumModels sampled models.
%
%       @see dfs_sample_model.

dfs_sample_models(N,MS) :-
        dfs_sample_models_(N,0,MS).

dfs_sample_models_(N,N,[]) :- !.
dfs_sample_models_(N,I,[M|MS]) :-
        I0 is I + 1,
        dfs_sample_model(M),
        dfs_pprint_model(M),
        dfs_sample_models_(N,I0,MS).

%!      dfs_sample_model(-Model) is det.
%
%       Sample a model from the world specificiations.

dfs_sample_model((Um,Vm)) :-
        constants_and_universe(Consts,Um),
        dfs_init_g((Um,_),G),
        dfs_vector_space:ifunc_inst_constants(Consts,Um,VmCs),
        dfs_constant_instantiations((_,VmCs),CIs),
        findall(P,property(P),Ps),
        findall(C,constraint(C),Cs),
        optimize_constraints(Cs,OCs),
        dfs_sample_properties(Ps,Um,G,CIs,OCs,VmCs,Vm).

%!      constants_and_universe(-Constants,-Entities) is det.

constants_and_universe(Cs,Um) :-
        findall(C,constant(C),Cs),
        length(Cs,N),
        dfs_entities(N,Um).

%!      dfs_sample_properties(+Properties,+Universe,+G,+ConstInstantiations,
%!              +Constraints,+IFuncConstants,-IFunc) is det.
%
%       Samples property instantiations using a non-deterministic,
%       probabilistic and incremental inference-driven sampling algorithm.
%
%       The aim is to arrive at an interpretation function that satisfies a
%       set of imposed probabilistic and hard constraints. To this end, we 
%       start out with with an empty interpretation function, to which we will
%       incrementally add properties. We call this interpretation function the
%       Light World (LVm), and this function will contain all properties that
%       are true in the model. In parallel to the Light World, we will also
%       construct a Dark World (DVm) function that will contain all properties
%       that are false in the model. 
%
%       Given LVm and DVm, a set of randomly ordered properties P, and a set
%       of constraints C, we then do the following for each property p:
%
%       (1) Add p to LVm, yielding LVm';
%
%       (2) LT = true iff for each constraint c:
%       
%           -- c is satisfied by LVm' (-> c is true);
%           -- or if the complement of c is not satisfied by DVm
%              (-> c is not untrue).
%
%       (3) Add p to DVm, yielding DVm';
% 
%       (4) DT = true iff for each constraint c:
%       
%           -- c is satisfied by LVm (-> c is true);
%           -- or if the complement of c is not satisfied by DVm'.
%              (-> c is not untrue).
%
%       (5) Depending on the outcome of (2) and (4):
%
%           -- LT & DT: Infer p with Pr(p): LVm = LVm', otherwise: DVm = DVm'
%           -- LT & !DT: Infer p to be true in the Light World: LVm = LVm'
%           -- !LT & DT: Infer p to be true in the Dark World: DVm = DVm'
%           -- !LT & !DT: The model is inconsistent, and will be discarded.
%
%       (6) Repeat (1) for next p. If each p is a property in either LVm or
%           DVm, and LVm satisfies all constraints, LVm is the final 
%           interpretation function.

dfs_sample_properties(Ps,Um,G,CIs,Cs,VmCs,Vm) :-
        random_permutation(Ps,Ps1),
        dfs_sample_properties_(Ps1,Um,G,CIs,Cs,VmCs,VmCs,Vm), !.
dfs_sample_properties(Ps,Um,G,CIs,Cs,VmCs,Vm) :-
        debug(dfs_sampling,'Restarting sample ...',[]),
        dfs_sample_properties(Ps,Um,G,CIs,Cs,VmCs,Vm).

dfs_sample_properties_([],Um,G,_,Cs,Vm,_,Vm) :-
        validate_sample_model(Cs,(Um,Vm),G).
dfs_sample_properties_([P|Ps],Um,G,CIs,Cs,LVm0,DVm0,LVm) :-
        P =.. [Prop|Args],
        dfs_terms_to_entities(Args,CIs,Es),
        add_property(LVm0,Prop,Es,LVm1),
        ( satisfies_constraints(Cs,(Um,LVm1),(Um,DVm0),G) -> LT = 1 ; LT = 0 ),     %% light world
        add_property(DVm0,Prop,Es,DVm1),
        ( satisfies_constraints(Cs,(Um,LVm0),(Um,DVm1),G) -> DT = 1 ; DT = 0 ),     %% dark world
        (  LT == 1, DT == 1             %% undecided
        -> (  probabilistic_choice(P,(Um,LVm0),G)
           -> debug(dfs_sampling,'(flip to light ): ~w',[P]),
              dfs_sample_properties_(Ps,Um,G,CIs,Cs,LVm1,DVm0,LVm)
           ;  debug(dfs_sampling,'(flip to dark  ): ~w',[P]),
              dfs_sample_properties_(Ps,Um,G,CIs,Cs,LVm0,DVm1,LVm) )
        ;  (  LT == 1, DT == 0          %% light world
           -> debug(dfs_sampling,'[infer to light]: ~w',[P]),
              dfs_sample_properties_(Ps,Um,G,CIs,Cs,LVm1,DVm0,LVm)
           ;  (  LT == 0, DT == 1       %% dark world
              -> debug(dfs_sampling,'[infer to dark ]: ~w',[P]),
                 dfs_sample_properties_(Ps,Um,G,CIs,Cs,LVm0,DVm1,LVm)
              ;  debug(dfs_sampling,'{inconsistency }: ~w',[P]),
                 with_output_to(atom(LW),dfs_pprint_propositions((Um,LVm0))),
                 debug(dfs_sampling,'Light world: ~a',[LW]),
                 with_output_to(atom(DW),dfs_pprint_propositions((Um,DVm0))),
                 debug(dfs_sampling,'Dark world : ~a',[DW]),
                 false ) ) ).           %% inconsistent

%!      validate_sample_model(+Constraints,+LightModel,+G) is semidet.
%
%       True iff LightModel satisfies all constraints.

validate_sample_model([],_,_).
validate_sample_model([C|Cs],M,G) :-
        dfs_interpret(C,M,G), !,
        validate_sample_model(Cs,M,G).
validate_sample_model([C|_],_,_) :-
        dfs_io:format_formula(C,F),
        debug(dfs_sampling,'Failed to satisfy: ~a',[F]),
        false.

%!      add_property(+IFunc,+Property,+Entities,-IFunc) is det.
%
%       Adds a property for a set of entities to an interpretation function.

add_property([],Prop,[E|Es],[P1]) :-
        (  Es == []
        -> P1 =.. [Prop|[[E]]]          %% unary predicates
        ;  P1 =.. [Prop|[[[E|Es]]]] ).  %% n-ary predicates
add_property([P0|P0s],Prop,[E|Es],[P1|P0s]) :-
        P0 =.. [Prop|_], !,
        (  Es == []
        -> P0 =.. [Prop|[Es0]],         %% unary predicates
           P1 =.. [Prop|[[E|Es0]]]      
        ;  P0 =.. [Prop|[Es0]],         %% n-ary predicates
           P1 =.. [Prop|[[[E|Es]|Es0]]] ).
add_property([P0|P0s],Prop,Es,[P0|P1s]) :-
        add_property(P0s,Prop,Es,P1s).

%!      satisfies_constraints(+Constraints,+LightMdl,+DarkMdl,+G) is semidet.
%
%       True when each constraint is either satisfied in the light world, or
%       when its complement is not satisfied in the dark world.

satisfies_constraints([],_,_,_).
satisfies_constraints([C|Cs],LM,DM,G) :-
        dfs_interpret(C,LM,G), !,
        satisfies_constraints(Cs,LM,DM,G).
satisfies_constraints([C|Cs],LM,DM,G) :-
        dfs_complement(C,Cc),
        \+ dfs_interpret(Cc,DM,G),
        satisfies_constraints(Cs,LM,DM,G).

%!      probabilistic_choice(+Formula,+Model,+G) is semidet.
%
%       Probabilistically determines a truth value for Formula, given a Model
%       (thus far) and assignment function G. Succeeds upon true, and fails
%       upon falls.

probabilistic_choice(P,M,G) :-
        probability(P,C,Pr),
        dfs_interpret(C,M,G),
        !,
        maybe(Pr).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% constraint optimization %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      optimize_constraints(+Constraints,-OptimizedConstraints) is det.
%
%       @see optimize_constraint/2.

optimize_constraints(Cs,OCs) :-
        optimize_constraints_(Cs,[],OCs0),
        reverse(OCs0,OCs).

optimize_constraints_([],OCs,OCs).
optimize_constraints_([C|Cs],OCsAcc,OCs) :-
        optimize_constraint(C,OC),
        append(OC,OCsAcc,OCsAcc0),
        optimize_constraints_(Cs,OCsAcc0,OCs).

%!      optimize_constraint(+Formula,-FormulaSet) is det.
%
%       Optimizes a Formula for incremental, inference-driven sampling,
%       yielding a set of optimized formulas. A number of different
%       optimization stragegies are employed: 
%
%       1) Simplification:
%       -- double negation elimination: !!P => P
%
%       2) Quantifier transformation:
%       -- negated univeral quantification: !∀x P => ∃x !P
%
%       3) Conjunct isolation:
%       -- using & and | distributivity: (P & Q) | (P & Z) => P & (Q | Z)
%       -- using de Morgan's laws: !(P | Q) => !Q & !P 
%       -- using existential quantifier scoping:
%               ∃x (P & Q) => P & ∃x Q (iff x is not free in P)
%               ∃x (P & Q) => Q & ∃x P (iff x is not free in Q)
%       -- using universal quantifier scoping:
%               ∀x (P & Q) => P & ∀x Q (iff x is not free in P)
%               ∀x (P & Q) => Q & ∀x P (iff x is not free in Q)
%
%       3) Conjunct splitting:
%       -- transform P & Q into a set {P,Q}
%
%       4) Quantifier domain restriction (see below).

optimize_constraint(neg(neg(P)),Ps) :-
        !, % !!P => P
        optimize_constraint(P,Ps).
optimize_constraint(neg(forall(X,P)),Ps) :-
        !, % !∀x P => ∃x !P
        optimize_constraint(exists(X,neg(P)),Ps).
optimize_constraint(or(and(P,Q),and(P,Z)),Ps) :-
        !, % (P & Q) | (P & Z) => P & (Q | Z)
        optimize_constraint(and(P,or(Q,Z)),Ps).
optimize_constraint(neg(or(P,Q)),Ps) :-
        !, % !(P | Q) => !Q & !P 
        optimize_constraint(and(neg(P),neg(Q)),Ps).
optimize_constraint(exists(X,and(P,Q)),Ps) :-
        !, % ∃x (P & Q) => P & ∃x Q (iff x is not free in P)
           % ∃x (P & Q) => Q & ∃x P (iff x is not free in Q)
        vis(P,[],[],VIs),
        (  memberchk(X=_,VIs)   %% assume x is free in either P or Q
        -> optimize_constraint(and(P,exists(X,Q)),Ps)
        ;  optimize_constraint(and(Q,exists(X,P)),Ps) ).
optimize_constraint(forall(X,and(P,Q)),Ps) :-
        !, % ∀x (P & Q) => P & ∀x Q (iff x is not free in P)
           % ∀x (P & Q) => Q & ∀x P (iff x is not free in Q)
        vis(P,[],[],VIs),
        (  memberchk(X=_,VIs)   %% assume x is free in either P or Q
        -> optimize_constraint(and(P,forall(X,Q)),Ps)
        ;  optimize_constraint(and(Q,forall(X,P)),Ps) ).
optimize_constraint(and(P,Q),Ps) :-
        !, % P & Q => {P,Q}
        optimize_constraint(P,P0),
        optimize_constraint(Q,Q0),
        append(P0,Q0,Ps).
optimize_constraint(P,Ps) :-
        restrict_q_domains(P,Ps).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% quantifier domain restriction %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%!      restrict_q_domains(+Formula,-OptimizedFormulaSet) is det.
%
%       Optimizes constraints that involve existential and universal
%       quantifiers by domain restriction.
%
%       Existential quantification: given an existentially quantified formula,
%       e.g., exists(x,p(x)), the model-theoretic interpreter implemented by
%       dfs_interpret/3 will evaluate its truth by filling in each entity in
%       the universe for x, until p(x) is true. However, given the set of 
%       atomic propositions (properties), not all of the entities in the 
%       universe may be possible arguments for p/1. Hence, we can optimize the
%       constraint by disjoining p(x) for all possible instances of x.
%
%       Universal quantification: given a chain of universal quantifiers
%       ending in an implication, e.g., forall(x,forall(y,imp(p(x),q(x,y)))),
%       the model-theoretic interpreter will evaluate its truth by filling in
%       each entity in the universe for x and y. Again, given the set of 
%       atomic propositions (properties), however, not all of the entities in
%       the universe may be possible arguments for p/1 and q/2. Hence, as the
%       implication conditions the truth value of the statement on p(x), we
%       can optimize the constraint by rewriting it as a set of implications
%       for possible arguments for p(x) and q(x,y) only.

restrict_q_domains(P,FIs) :-
        vis(P,[],[],VIs),
        findall(FI,fi(P,VIs,FI),FIs).

%!      fi(+Formula,+VarInsts,-FormulaInstance) is nondet.
%
%       Returns a domain-restricted instance of Formula, by filling in 
%       possible arguments for the quantified variables.

fi(neg(P0),     VIs,neg(P1)     ) :- !, fi(P0,VIs,P1).
fi(and(P0,Q0),  VIs,and(P1,Q1)  ) :- !, fi(P0,VIs,P1), fi(Q0,VIs,Q1).
fi(or(P0,Q0),   VIs,or(P1,Q1)   ) :- !, fi(P0,VIs,P1), fi(Q0,VIs,Q1).
fi(exor(P0,Q0), VIs,exor(P1,Q1) ) :- !, fi(P0,VIs,P1), fi(Q0,VIs,Q1).
fi(imp(P0,Q0),  VIs,imp(P1,Q1)  ) :- !, fi(P0,VIs,P1), fi(Q0,VIs,Q1).
fi(iff(P0,Q0),  VIs,iff(P1,Q1)  ) :- !, fi(P0,VIs,P1), fi(Q0,VIs,Q1).
fi(exists(X,P0),VIs,P1) :-                                      /* +optimization */
        !, findall(FI,(select_vi(X,VIs,VIs0),fi(P0,VIs0,FI)),FIs),
        dfs_disjoin(FIs,P1).
%fi(exists(X,P0),VIs,exists(X,P1)) :- !, fi(P0,VIs,P1).         /* -optimization */
fi(forall(X,P0),VIs,P1) :-
        q_imp_chain(X,forall(X,P0)), !,
        select_vi(X,VIs,VIs0),
        fi(P0,VIs0,P1).
fi(forall(X,P0),VIs,forall(X,P1)) :- !, fi(P0,VIs,P1).
fi(top,_,top) :- !.
fi(bottom,_,bottom) :- !.
fi(P0,VIs,P1) :-
        prop_instance(P0,VIs,P1).

%!      select_vi(+Var,+OldVarInsts,-NewVarInsts) is nondet.
%
%       Selects a single variable instantiation of Var=X from OldVarInsts,
%       yielding NewVarInsts in which Var=X is the only instantiation of Var.

select_vi(V,VIs,[V=X|VIs1]) :-
        findall(V=X,member(V=X,VIs),VIs0),
        findall(V1=Y,(member(V1=Y,VIs),V1\=V),VIs1),
        select(V=X,VIs0,_).

%!      prop_instance(+Prop,+VarInsts,-PropInstance) is nondet.
%
%       Returns an instance of a property. If Prop contains variables, these
%       will be filled in using the instantiations in VarInsts. Otherwise,
%       Prop remains unchanged.

prop_instance(P,VIs,PI) :-
        P =.. [Prop|As],
        prop_instance_(As,VIs,AIs),
        PI =.. [Prop|AIs].

prop_instance_([],_,[]).
prop_instance_([A|As],VIs,[E|IAs]) :-
        memberchk(A=E,VIs), !,
        prop_instance_(As,VIs,IAs).
prop_instance_([A|As],VIs,[A|IAs]) :-
        prop_instance_(As,VIs,IAs).

%!      vis(+Formula,+VarsAcc,+VarInstsAcc,-VarInsts) is det.
%
%       Returns all possible instances of variables that occur in an
%       antecedent of an implication that ends a chain of universal
%       quantifiers.

vis(neg(P),     Vs,VIs0,VIs1) :- !, vis(P,Vs,VIs0,VIs1).
vis(and(P,Q),   Vs,VIs0,VIs2) :- !, vis(P,Vs,VIs0,VIs1), vis(Q,Vs,VIs1,VIs2).
vis(or(P,Q),    Vs,VIs0,VIs2) :- !, vis(P,Vs,VIs0,VIs1), vis(Q,Vs,VIs1,VIs2).
vis(exor(P,Q),  Vs,VIs0,VIs2) :- !, vis(P,Vs,VIs0,VIs1), vis(Q,Vs,VIs1,VIs2).
vis(imp(P,Q),   Vs,VIs0,VIs2) :- !, vis(P,Vs,VIs0,VIs1), vis(Q,Vs,VIs1,VIs2).
vis(iff(P,Q),   Vs,VIs0,VIs2) :- !, vis(P,Vs,VIs0,VIs1), vis(Q,Vs,VIs1,VIs2).
vis(exists(X,P),Vs,VIs0,VIs1) :- !, vis(P,[X|Vs],VIs0,VIs1).    /* +optimization */
vis(exists(_,P),Vs,VIs0,VIs1) :- !, vis(P,Vs,VIs0,VIs1).        /* -optimization */
vis(forall(X,P),Vs,VIs0,VIs1) :-
        !,
        (  q_imp_chain(X,forall(X,P))
        -> vis(P,[X|Vs],VIs0,VIs1)
        ;  vis(P,Vs,VIs0,VIs1) ).
vis(top,_,VIs0,VIs0) :- !.
vis(bottom,_,VIs0,VIs0) :- !.
vis(P,Vs,VIs0,VIs1) :-
        vis_(P,Vs,VIs0,VIs1).

vis_(_,[],VIs,VIs) :- !.
vis_(P,[V|Vs],VIs0,VIs4) :-
        prop_template(P,V,Templ,X), !,
        findall(V=X,property(Templ),VIs1),
        list_to_ord_set(VIs1,VIs2),
        union(VIs0,VIs2,VIs3),
        vis_(P,Vs,VIs3,VIs4).
vis_(P,[_|Vs],VIsAcc,VIs) :-
        vis_(P,Vs,VIsAcc,VIs).

%!      q_imp_chain(+Variable,+Formula) is semidet.
%
%       True iff Formula is a universal quantifier chain ending in an
%       implication, in which Variable occurs in the antecedent.

q_imp_chain(X,forall(_,imp(P,_))) :- 
        vis(P,[X],[],VIs),
        memberchk(X=_,VIs), !.
q_imp_chain(X,forall(_,P)) :-
        q_imp_chain(X,P).

%!      prop_template(+Prop,+Variable,-Template,-BoundVar) is det.
%
%       Constructs a template for Prop in which Variable is bound to BoundVar,
%       and all other arguments are replaced by wildcards:
%
%       ==
%       Prop = p(x,y,z), Variable = y ==> Template = p(_, BoundVar, _).
%       ==

prop_template(P,V,Templ,X) :-
        P =.. [Prop|As],
        memberchk(V,As),
        prop_template_(As,V,TAs,X),
        Templ =.. [Prop|TAs].

prop_template_([],_,[],_).
prop_template_([V|As],V,[X|TAs],X) :-
        !, prop_template_(As,V,TAs,X).
prop_template_([_|As],V,[_|TAs],X) :-
        prop_template_(As,V,TAs,X).
