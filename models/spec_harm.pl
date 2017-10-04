:- use_module('../src/dfs_main.pl').

@+ Person :- person(Person).
@+ Place  :- place(Place).
@+ Food   :- food(Food).
@+ Drink  :- drink(Drink).

@* enter(Person,Place)   :- person(Person), place(Place).
@* ask_menu(Person)      :- person(Person).
@* order(Person,Order)   :- person(Person), food(Order).
@* order(Person,Order)   :- person(Person), drink(Order).
@* eat(Person,Food)      :- person(Person), food(Food).
@* drink(Person,Drink)   :- person(Person), drink(Drink).
@* pay(Person)           :- person(Person).
@* leave(Person)         :- person(Person).

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

1.0 <- ( order(X,Y) | or(eat(X,Y),drink(X,Y))            ).
1.0 <- ( order(X,_) | and(exists(y,enter(X,y)),pay(X))   ).
1.0 <- ( pay(X)     | and(leave(X),exists(y,order(X,y))) ).
0.5 <- ( _          | top                                ). % <- coin flip

% If a person eats or drinks something, he must have ordered it.

@# forall(x,forall(y,imp(eat(x,y),order(x,y)))).
@# forall(x,forall(y,imp(drink(x,y),order(x,y)))).

% If has entered somewhere and pays, he must have ordered something.

@# forall(x,imp(pay(x),forall(y,imp(enter(x,y),exists(z,order(x,z)))))).

% If a person has seen the menu and pays, he must have ordered something.

@# forall(x,imp(and(ask_menu(x),pay(x)),exists(y,order(x,y)))).

% If a person leaves and has ordered something, he must have paid.

@# forall(x,imp(leave(x),forall(y,imp(order(x,y),pay(x))))).

% A person can only enter a single place.

@# forall(x,forall(y,imp(enter(x,y),neg(exists(z,and(enter(x,z),neg(z=y))))))).

%%%%%%%%%%%%%%%
%% sentences %%
%%%%%%%%%%%%%%%

s(drink(X,Y)) --> [X, drinks, Y], { person(X), drink(Y) }.
