:- use_module('../src/dfs_main.pl').

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

%% persons

person('beth').
person('dave').
person('thom').

%% places

place('cinema').
place('restaurant').

%% orders

food('dinner').
food('popcorn').

drink('water').
drink('cola').
drink('champagne').

probability(order(X,Y), or(eat(X,Y),drink(X,Y)),                1.0).
probability(order(X,_), and(exists(y,enter(X,y)),pay(X)),       1.0).
probability(order(X,_), and(ask_menu(X),pay(X)),                1.0).
probability(pay(X),     and(leave(X),exists(y,order(X,y))),     1.0).
probability(_,          top,                                    0.5). % <- coin flip

%constraint(exists(x,exists(y,eat(x,y)))).
%constraint(exists(x,exists(y,drink(x,y)))).

% If a person eats or drinks something, he must have ordered it.

constraint(forall(x,forall(y,imp(eat(x,y),order(x,y))))).
constraint(forall(x,forall(y,imp(drink(x,y),order(x,y))))).

%constraint(forall(x,forall(y,imp(or(eat(x,y),drink(x,y)),order(x,y))))).

% % If has entered somewhere and pays, he must have ordered something.
constraint(forall(x,imp(pay(x),forall(y,imp(enter(x,y),exists(z,order(x,z))))))).

% % If a person has seen the menu and pays, he must have ordered something.
constraint(forall(x,imp(and(ask_menu(x),pay(x)),exists(y,order(x,y))))).

% % If a person leaves and has ordered something, he must have paid.
constraint(forall(x,imp(leave(x),forall(y,imp(order(x,y),pay(x)))))).

% % A person can only enter a single place.
% constraint(forall(x,forall(y,imp(enter(x,y),forall(z,imp(enter(x,z),z=y)))))).
constraint(forall(x,forall(y,imp(enter(x,y),neg(exists(z,and(enter(x,z),neg(z=y)))))))).

% % A person can only order a single type of food.
%constraint(forall(x,forall(y,imp(order(x,y),forall(z,imp(order(x,z),z=y)))))).
