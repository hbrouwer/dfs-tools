/*
 * Copyright 2019 Noortje Venhuizen <njvenhuizen@gmail.com>
 *     and Harm Brouwer <me@hbrouwer.eu>
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

:- use_module('../src/dfs_main.pl').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                              M O D E L                                %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Constants and Predicates %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constant(Person) :- 
        person(Person).
constant(Place) :- 
        place(Place).
constant(Food) :-
        food(Food).
constant(Drink) :- 
        drink(Drink).

property(enter(Person,Place)) :-
        person(Person),
        place(Place).

property(ask_menu(Person)) :-
        person(Person).

property(order(Person,Order)) :-
        person(Person),
        food(Order).
property(order(Person,Order)) :-
        person(Person),
        drink(Order).

property(eat(Person,Food)) :-
        person(Person),
        food(Food).

property(drink(Person,Drink)) :-
        person(Person),
        drink(Drink).

property(pay(Person)) :-
        person(Person).

property(leave(Person)) :-
        person(Person).

%%% Variable instantiations %%%

person('john').
person('ellen').

place('restaurant').
place('bar').

food('pizza').
food('fries').

drink('wine').
drink('beer').

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Hard Constraints %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%% Leaving and Entering %%%%%%%%

%% A person can only enter a single place.
constraint(imp(enter(P,L),neg(exists(x,and(neg(x=L),enter(P,x)))))) :- 
        person(P), 
        place(L).

%%%%%%%% Ordering %%%%%%%%

%% If a person eats something, he must have ordered it.
constraint(imp(eat(P,F),order(P,F))) :-
        person(P),
        food(F).

%% If a person drinks something, he must have ordered it.
constraint(imp(drink(P,D),order(P,D))) :-
        person(P),
        drink(D).

%% If has entered somewhere and pays, he must have ordered something.
constraint(imp(and(enter(P,L),pay(P)),exists(x,order(P,x)))) :-
        person(P),
        place(L).

%% If a person has seen the menu and pays, he must have ordered something.
constraint(imp(and(ask_menu(P),pay(P)),exists(x,order(P,x)))) :-
        person(P).

%%%%%%%% Paying %%%%%%%%

%% If a person leaves and has ordered something, he must have paid
% (except if someone else went to the same place, and already paid).
constraint(imp(and(exists(x,order(P,x)),leave(P)),or(pay(P),exists(y,and(neg(y=P),exists(z,and(enter(P,z),and(enter(y,z),pay(y))))))))) :-
        person(P).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                      P R O B A B I L I T I E S                        %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Base probabilities
probability(enter('john','restaurant'),top,0.6).
probability(enter('john','bar'),top,0.4).
probability(order('john','beer'),top,0.8).
probability(order('john','wine'),top,0.2).
probability(enter('ellen','restaurant'),top,0.6).
probability(enter('ellen','bar'),top,0.4).
probability(order('ellen','beer'),top,0.2).
probability(order('ellen','wine'),top,0.8).

% %% Probability of person entering the restaurant
% %% * increases if he/she ordered pizza
% %% * decreases if he/she ordered fries
probability(enter(P,'restaurant'),order(P,'pizza'),0.9) :- person(P).
probability(enter(P,'restaurant'),order(P,'fries'),0.1) :- person(P).

% %% Probability of person entering the bar
% %% * increases if he/she ordered fries
% %% * decreases if he/she ordered pizza
probability(enter(P,'bar'),order(P,'pizza'),0.1) :- person(P).
probability(enter(P,'bar'),order(P,'fries'),0.9) :- person(P).

% %% Probability of person entering a place
% %% * increases if someone else already entered it
probability(enter(P1,L),enter(P2,L),0.9) :- person(P1), person(P2), place(L).

% %% Probability of person ordering pizza
% %% * increases if he/she went to the restaurant
% %% * decreases if he/she went to the bar
probability(order(P,'pizza'),enter(P,'restaurant'),0.9) :- person(P).
probability(order(P,'pizza'),enter(P,'bar'),0.1) :- person(P).

% %% Probability of person ordering fries
% %% * increases if he/she went to the bar
% %% * decreases if he/she went to the restaurant
probability(order(P,'fries'),enter(P,'restaurant'),0.1) :- person(P).
probability(order(P,'fries'),enter(P,'bar'),0.9) :- person(P).

% %% Probability of person ordering food/drink
% %% * decreases if he/she already ordered food/drink
probability(order(P,O1),order(P,O2),0.1) :- person(P), food(O1), food(O2).
probability(order(P,O1),order(P,O2),0.1) :- person(P), drink(O1), drink(O2).

% %% Probability of person drinking something
% %% * increases if he/she has ordered it
% %% * decreases if he/she has ordered another drink
probability(drink(P,D),order(P,D),0.9) :- person(P), drink(D).
probability(drink(P,D1),order(P,D2),0.1) :- person(P), drink(D1), drink(D2).

% %% Probability of person eating something
% %% * increases if he/she has ordered it
% %% * decreases if he/she has ordered other food
probability(eat(P,F),order(P,F),0.9) :- person(P), food(F).
probability(eat(P,F1),order(P,F2),0.1) :- person(P), food(F1), food(F2).

% Otherwise: coin flip
probability(_,top,0.5).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                           S E N T E N C E S                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%% Structures %%%%

sentence((Sen,Sem)) :- s_simpl(Sem,Sen,[]).
sentence((Sen,Sem)) :- s_coord(Sem,Sen,[]).

%%%% Sentences %%%%
s_simpl(Sem) --> np1(N), vp(_,N,_,Sem).
s_coord(Sem) --> np1(N), vp(V,N,O,_), vp_coord(V,N,O,Sem).

%%%% Constituents %%%%

np1(john)     --> ['john'].
np1(ellen)    --> ['ellen'].
np1(someone)  --> ['someone'].
np1(everyone) --> ['everyone'].

np2(place,restaurant) --> ['the','restaurant'].
np2(place,bar) --> ['the','bar'].

np2(food,pizza) --> ['pizza'].
np2(food,fries) --> ['fries'].

np2(drink,beer) --> ['beer'].
np2(drink,wine) --> ['wine'].

%%%% Main Clause VPs %%%%

vp(enter,N,P,Sem)    --> ['entered'], np2(place,P),
        { sbj_semantics(N,S,Q),
          qtf_semantics(enter,S,Q,[P],Sem) }.

vp(ask_menu,N,_,Sem) --> ['asked','for','the','menu'],
        { sbj_semantics(N,S,Q),
          qtf_semantics(ask_menu,S,Q,[],Sem) }.

vp(order,N,D,Sem)    --> ['ordered'], np2(drink,D),
        { sbj_semantics(N,S,Q),
          qtf_semantics(order,S,Q,[D],Sem) }.

vp(order,N,F,Sem)    --> ['ordered'], np2(food,F),
        { sbj_semantics(N,S,Q),
          qtf_semantics(order,S,Q,[F],Sem) }.

vp(eat,N,F,Sem)      --> ['ate'], np2(food,F),
        { sbj_semantics(N,S,Q),
          qtf_semantics(eat,S,Q,[F],Sem) }.

vp(drink,N,D,Sem)    --> ['drank'], np2(drink,D),
        { sbj_semantics(N,S,Q),
          qtf_semantics(drink,S,Q,[D],Sem) }.

vp(pay,N,_,Sem)      --> ['paid'],
        { sbj_semantics(N,S,Q),
          qtf_semantics(pay,S,Q,[],Sem) }.

vp(leave,N,_,Sem)    --> ['left'],
        { sbj_semantics(N,S,Q),
          qtf_semantics(leave,S,Q,[],Sem) }.

%%%% Coordinated VPs %%%%

vp_coord(enter,N,O1,Sem) --> ['and'], vp(ask_menu,N,_,_),
        { sbj_semantics(N,S,Q),
          crd_semantics(enter,[O1],ask_menu,[],S,Q,Sem) }.
vp_coord(enter,N,O1,Sem) --> ['and'], vp(order,N,O2,_),
        { sbj_semantics(N,S,Q),
          crd_semantics(enter,[O1],order,[O2],S,Q,Sem) }.
vp_coord(enter,N,O1,Sem) --> ['and'], vp(leave,N,_,_),
        { sbj_semantics(N,S,Q),
          crd_semantics(enter,[O1],leave,[],S,Q,Sem) }.

vp_coord(ask_menu,N,_,Sem) --> ['and'], vp(order,N,O2,_),
        { sbj_semantics(N,S,Q),
          crd_semantics(ask_menu,[],order,[O2],S,Q,Sem) }.
vp_coord(ask_menu,N,_,Sem) --> ['and'], vp(leave,N,_,_),
        { sbj_semantics(N,S,Q),
          crd_semantics(ask_menu,[],leave,[],S,Q,Sem) }.

vp_coord(pay,N,_,Sem) --> ['and'], vp(leave,N,_,_),
        { sbj_semantics(N,S,Q),
          crd_semantics(pay,[],leave,[],S,Q,Sem) }.

%%%% Semantics %%%%

% Subject Semantics
sbj_semantics(P,[P],'nq') :- person(P). % john, ellen
sbj_semantics(someone,[john,ellen],'eq').
sbj_semantics(everyone,[john,ellen],'uq').

% Quantifier Semantics
% Adapted from dss_semantics_event/4
qtf_semantics(Pred,[S],_,Os,Sem) :- !, 
        Sem =.. [Pred,S|Os].
qtf_semantics(Pred,[S|Ss],'eq',Os,or(Sem0,Sem1)) :- !,
        Sem0 =.. [Pred,S|Os],
        qtf_semantics(Pred,Ss,'eq',Os,Sem1).
qtf_semantics(Pred,[S|Ss],'uq',Os,and(Sem0,Sem1)) :-
        Sem0 =.. [Pred,S|Os],
        qtf_semantics(Pred,Ss,'uq',Os,Sem1).

% Coordination Semantics
crd_semantics(P1,Os1,P2,Os2,[S],_,and(Sem0,Sem1)) :- !, 
        Sem0 =.. [P1,S|Os1],
        Sem1 =.. [P2,S|Os2].
crd_semantics(P1,Os1,P2,Os2,[S|Ss],'eq',or(Sem0,Sem1)) :-
        !, crd_semantics(P1,Os1,P2,Os2,[S],'eq',Sem0),
        crd_semantics(P1,Os1,P2,Os2,Ss,'eq',Sem1).
crd_semantics(P1,Os1,P2,Os2,[S|Ss],'uq',and(Sem0,Sem1)) :-
        crd_semantics(P1,Os1,P2,Os2,[S],'uq',Sem0),
        crd_semantics(P1,Os1,P2,Os2,Ss,'uq',Sem1).
