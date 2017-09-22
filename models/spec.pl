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

probability(_,_,0.5).


%% If a person eats something, he must have ordered it.
%constraint(forall(x,forall(y,imp(eat(x,y),order(x,y))))).

%% If a person drinks something, he must have ordered it.
%constraint(forall(x,forall(y,imp(drink(x,y),order(x,y))))).

%% If has entered somewhere and pays, he must have ordered something.
%constraint(forall(x,forall(y,imp(and(enter(x,y),pay(x)),exists(z,order(x,z)))))).

%% If a person has seen the menu and pays, he must have ordered something.
%constraint(forall(x,imp(and(ask_menu(x),pay(x)),exists(y,order(x,y))))).

%%%%%%%% Paying %%%%%%%%

%% If a person leaves and has ordered something, he must have paid.
%constraint(forall(x,forall(y,imp(and(order(x,y),leave(x)),pay(x))))).

%constraint(forall(x,forall(y,imp(and(order(x,y),leave(x)),pay(x)))))).

 %% A person can only enter a single place.
%constraint(forall(x,neg(exists(y,exists(z,and(neg(y=z),and(enter(x,y),enter(x,z)))))))).

%% A person can only order a single type of food
%constraint(forall(x,forall(y,forall(z,imp(and(food(y),and(food(z),and(order(x,y),order(x,z)))),z=y))))).

%%%%%%%%%%
%%%%%%%%%%

%% A person can only enter a single place.
%forall(x,forall(y,forall(z,imp(and(enter(x,y),enter(x,z)),z=y))))

constraint(imp(exists(x,exists(y,(enter(x,y)))),
        forall(x,forall(y,imp(enter(x,y),forall(z,imp(enter(x,z),z=x))))))).

%% A person can only order a single type of food
%forall(x,forall(y,forall(z,imp(and(food(y),and(food(z),and(order(x,y),order(x,z)))),z=y))))

%% If a person eats something, he must have ordered it.
%forall(x,forall(y,imp(eat(x,y),order(x,y))))

constraint(imp(exists(x,exists(y,eat(x,y))),forall(x,forall(y,imp(eat(x,y),order(x,y)))))).


%% If a person drinks something, he must have ordered it.
constraint(imp(exists(x,exists(y,drink(x,y))),
        forall(x,forall(y,imp(drink(x,y),order(x,y)))))).

%% If has entered somewhere and pays, he must have ordered something.
%forall(x,forall(y,imp(and(enter(x,y),pay(x)),exists(z,order(x,z)))))

constraint(imp(exists(x,and(pay(x),exists(y,enter(x,y)))),
        forall(x,imp(pay(x),forall(y,imp(enter(x,y),exists(z,order(x,z)))))))).

%% If a person has seen the menu and pays, he must have ordered something.
%forall(x,imp(and(ask_menu(x),pay(x)),exists(y,order(x,y))))

constraint(imp(exists(x,and(ask_menu(x),pay(x))),
        forall(x,imp(and(ask_menu(x),pay(x)),exists(y,order(x,y)))))).

%% If a person leaves and has ordered something, he must have paid.
%forall(x,forall(y,imp(and(order(x,y),leave(x)),pay(x))))

constraint(imp(exists(x,and(leave(x),exists(y,order(x,y)))),
        forall(x,imp(leave(x),forall(y,imp(order(x,y),pay(x))))))).


