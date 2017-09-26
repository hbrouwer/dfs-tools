:- use_module('../src/dfs_main.pl').

constant(Person) :-
        person(Person).
constant(Place) :-
        place(Place).
constant(Food) :-
        food(Food).
constant(Drink) :-
        drink(Drink).

property(person(Person)) :-
        person(Person).
property(place(Place)) :-
        place(Place).
property(food(Food)) :-
        food(Food).
property(beverage(Drink)) :-
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

%% persons

person('beth').
person('dave').
person('thom').
% person('rick').
% person('morty').

%% places

place('cinema').
place('restaurant').
place('bar').

%% orders

food('dinner').
food('popcorn').
% food('kebap').
% food('frites').

drink('water').
drink('cola').
drink('champagne').
% drink('wine').
% drink('beer').

probability(pay(beth),_,0.5).
%probability(pay(dave),_,0.5).
%probability(pay(thom),_,0.5).
probability(_,_,0.5).

% constraint(person(thom)).
% constraint(person(beth)).
% constraint(person(dave)).

%constraint(forall(x,forall(y,imp(drink(x,y),and(person(x),beverage(y)))))).
%constraint(thom=thom).
% constraint(forall(x,imp(person(x),leave(x)))).
% constraint(exists(x,and(person(x),pay(x)))).

constraint(exists(x,person(x))).

% If a person eats or drinks something, he must have ordered it.
constraint(forall(x,imp(person(x),forall(y,imp(or(and(food(y),eat(x,y)),and(beverage(y),drink(x,y))),order(x,y)))))).

% % If has entered somewhere and pays, he must have ordered something.
constraint(forall(x,imp(and(person(x),pay(x)),forall(y,imp(and(place(y),enter(x,y)),exists(z,and(or(food(z),beverage(z)),order(x,z)))))))).

% % If a person has seen the menu and pays, he must have ordered something.
constraint(forall(x,imp(and(person(x),and(ask_menu(x),pay(x))),exists(y,and(or(food(y),beverage(y)),order(x,y)))))).

% % If a person leaves and has ordered something, he must have paid.
constraint(forall(x,imp(and(person(x),leave(x)),forall(y,imp(and(or(food(y),beverage(y)),order(x,y)),pay(x)))))).

% % A person can only enter a single place.
% %constraint(forall(x,neg(exists(y,exists(z,and(neg(y=z),and(enter(x,y),enter(x,z)))))))).
constraint(forall(x,imp(person(x),forall(y,imp(and(place(y),enter(x,y)),forall(z,imp(and(place(z),enter(x,z)),z=y))))))).

% % A person can only order a single type of food.
constraint(forall(x,imp(person(x),forall(y,imp(food(y),forall(z,imp(and(food(z),and(order(x,y),order(x,z))),z=y))))))).
