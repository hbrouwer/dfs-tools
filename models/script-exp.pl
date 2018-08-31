:- use_module('../src/dfs_main.pl').

coals_random_seed(1234).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                              M O D E L                                %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%
%%%% Constants %%%%
%%%%%%%%%%%%%%%%%%%

@+ Person    :- person(Person).
@+ Place     :- place(Place).
@+ Object    :- object(Object).
@+ Entity    :- entity(Entity).
@+ Predicate :- predicate(Predicate).

%%%%%%%%%%%%%%%%%%%%
%%%% Predicates %%%%
%%%%%%%%%%%%%%%%%%%%

% two-place predicates
@* enter(Person,Place)  :- person(Person), place(Place).
@* leave(Person,Place)  :- person(Person), place(Place).
@* open(Person,Object)  :- person(Person), object(Object). 

% referents
@* referent(Entity) :- person(Entity).
@* referent(Entity) :- place(Entity).
@* referent(Entity) :- object(Entity).
@* referent(Entity) :- entity(Entity).

@* event(Predicate) :- predicate(Predicate).

%%%%%%%%%%%%%%%%%%%
%%%% Variables %%%%
%%%%%%%%%%%%%%%%%%%

% persons
person(P) :- female(P).
person(P) :- male(P).

male('john').
female('mary').

% places
place('restaurant').
place('apartment').

% openable objects
object('menu').
object('mail').
object('umbrella').

% inferred entities
entity('waiter').
entity('table').
entity('bed').
entity('couch').

% predicates/events
predicate('enter').
predicate('leave').
predicate('open').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                       C O N S T R A I N T S                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Referents and events %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Each observation concerns only one person
@# imp(referent(Person1),neg(referent(Person2))) :-
        person(Person1), person(Person2), Person1 \= Person2.

% Predicates instantiate their event and associated referents
@# imp(enter(Person,Place),and(event('enter'),and(referent(Person),referent(Place)))) :-
        person(Person), place(Place).

@# imp(leave(Person,Place),and(event('leave'),and(referent(Person),referent(Place)))) :-
        person(Person), place(Place).

@# imp(open(Person,Object),and(event('open'),and(referent(Person),referent(Object)))) :-
        person(Person), object(Object).

% Places presuppose certain referential entities
@# imp(referent('restaurant'),and(referent('menu'),and(referent('waiter'),referent('table')))).
@# imp(referent('apartment'),and(referent('mail'),and(referent('bed'),referent('couch')))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Entering and Leaving %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% A person never enters and leaves
@# neg(and(enter(X,Y),leave(X,Z))) :- 
        person(X), place(Y), place(Z).       

% A person enters only one place
@# imp(enter(X,Y),neg(exists(z,and(neg(z=Y),enter(X,z))))) :- 
        person(X), place(Y).

% A person leaves only one place
@# imp(leave(X,Y),neg(exists(z,and(neg(z=Y),leave(X,z))))) :- 
        person(X), place(Y).

% A person opens only one object
@# imp(open(X,Y),neg(exists(z,and(neg(z=Y),open(X,z))))) :- 
        person(X), object(Y).

% Each observation contains an enter or leave event
@# imp(referent(P),exists(x,or(enter(P,x),leave(P,x)))) :-
        person(P).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                      P R O B A B I L I T I E S                        %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Referents and events %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Referents are only available through direct inference
0.0 <- ( referent(_)        | top ).

% Events are only available through direct inference
0.0 <- ( event(_)           | top ).

%%%%%%%%%%%%%%%%%%%%%%%
%%%% Opening items %%%%
%%%%%%%%%%%%%%%%%%%%%%%

% open(menu): enter(restaurant) > leave(restaurant), enter(apartment), leave(apartment)
0.9 <- ( open(P,'menu')        | enter(P,'restaurant') ). 
0.9 <- ( enter(P,'restaurant') | open(P,'menu') ). 
0.2 <- ( open(P,'menu')        | leave(P,'restaurant') ).
0.2 <- ( leave(P,'restaurant') | open(P,'menu') ).
0.2 <- ( open(P,'menu')        | enter(P,'apartment') ). 
0.2 <- ( enter(P,'apartment')  | open(P,'menu') ). 
0.2 <- ( open(P,'menu')        | leave(P,'apartment') ).
0.2 <- ( leave(P,'apartment')  | open(P,'menu') ).

% open(mail): enter(apartment) > leave(apartment), enter(restaurant), leave(restaurant)
0.9 <- ( open(P,'mail')        | enter(P,'apartment') ). 
0.9 <- ( enter(P,'apartment')  | open(P,'mail') ). 
0.2 <- ( open(P,'mail')        | leave(P,'apartment') ).
0.2 <- ( leave(P,'apartment')  | open(P,'mail') ). 
0.2 <- ( open(P,'mail')        | enter(P,'restaurant') ). 
0.2 <- ( enter(P,'restaurant') | open(P,'mail') ). 
0.2 <- ( open(P,'mail')        | leave(P,'restaurant') ).
0.2 <- ( leave(P,'restaurant') | open(P,'mail') ).

% open(umbrella): leave(restaurant), leave(apartment) > enter(restaurant), enter(apartment)
0.8 <- ( open(P,'umbrella')    | leave(P,'restaurant') ).
0.8 <- ( leave(P,'restaurant') | open(P,'umbrella') ).
0.8 <- ( open(P,'umbrella')    | leave(P,'apartment') ).
0.8 <- ( leave(P,'apartment')  | open(P,'umbrella') ).
0.2 <- ( open(P,'umbrella')    | enter(P,'restaurant') ).
0.2 <- ( enter(P,'restaurant') | open(P,'umbrella') ).
0.2 <- ( open(P,'umbrella')    | enter(P,'apartment') ).
0.2 <- ( enter(P,'apartment')  | open(P,'umbrella') ).

%%%%%%%%%%%%%%%%%%%
%%%% base case %%%%
%%%%%%%%%%%%%%%%%%%

0.5 <- ( _ | top ). % <- coin flip

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                           S E N T E N C E S                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Relations between places and objects
fit('restaurant','menu').
fit('apartment','mail').
nofit('apartment','menu').
nofit('restaurant','mail').

%%%%%%%%%%%%%%%%%%%%%
%%%% Frequencies %%%%
%%%%%%%%%%%%%%%%%%%%%

% FIT: enter(restaurant/apartment) ∧ open(menu/mail) (BASELINE)

@~ (Sen,Sem) :- s_fit(Sem,Sen,[]).
@~ (Sen,Sem) :- s_fit(Sem,Sen,[]).
@~ (Sen,Sem) :- s_fit(Sem,Sen,[]).
@~ (Sen,Sem) :- s_fit(Sem,Sen,[]).

% REL: leave(restaurant/apartment) ∧ open(menu/mail) (EVENT RELATED)

@~ (Sen,Sem) :- s_rel(Sem,Sen,[]).

% NOFIT: enter(apartment/restaurant) ∧ open(menu/mail) (EVENT UNRELATED)

@~ (Sen,Sem) :- s_nofit(Sem,Sen,[]).

% CTL_FIT: leave(restaurant/apartment) ∧ open(umbrella) 

@~ (Sen,Sem) :- s_ctl_fit(Sem,Sen,[]).
@~ (Sen,Sem) :- s_ctl_fit(Sem,Sen,[]).
@~ (Sen,Sem) :- s_ctl_fit(Sem,Sen,[]).
@~ (Sen,Sem) :- s_ctl_fit(Sem,Sen,[]).

% CTL_NOFIT1: leave(apartment/restaurant) ∧ open(menu/mail)

@~ (Sen,Sem) :- s_ctl_nofit1(Sem,Sen,[]).

% CTL_NOFIT2: enter(restaurant/apartment) ∧ open(umbrella) 

@~ (Sen,Sem) :- s_ctl_nofit2(Sem,Sen,[]).

%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Train sentences %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%

% FIT: enter(restaurant/apartment) ∧ open(menu/mail) (BASELINE)

s_fit(and(enter(P,L),open(P,O))) --> 
                [P, 'entered', 'the', L, 'and', 'he', 'opened', 'the', O],
                { male(P), fit(L,O) }. 
s_fit(and(enter(P,L),open(P,O))) --> 
                [P, 'entered', 'the', L, 'and', 'she', 'opened', 'the', O],
                { female(P), fit(L,O) }.    

% REL: leave(restaurant/apartment) ∧ open(menu/mail) (EVENT RELATED)

s_rel(and(leave(P,L),open(P,O))) --> 
                [P, 'left', 'the', L, 'and', 'he', 'opened', 'the', O],
                { male(P), fit(L,O) }. 
s_rel(and(leave(P,L),open(P,O))) --> 
                [P, 'left', 'the', L, 'and', 'she', 'opened', 'the', O],
                { female(P), fit(L,O) }.  

% NOFIT: enter(apartment/restaurant) ∧ open(menu/mail) (EVENT UNRELATED)

s_nofit(and(enter(P,L),open(P,O))) --> 
                [P, 'entered', 'the', L, 'and', 'he', 'opened', 'the', O],
                { male(P), nofit(L,O) }. 
s_nofit(and(enter(P,L),open(P,O))) --> 
                [P, 'entered', 'the', L, 'and', 'she', 'opened', 'the', O],
                { female(P), nofit(L,O) }.

% CTL_FIT: leave(restaurant/apartment) ∧ open(umbrella) 

s_ctl_fit(and(leave(P,L),open(P,'umbrella'))) --> 
              [P, 'left', 'the', L, 'and', 'he', 'opened', 'the', 'umbrella'],
                { male(P), fit(L,_) }. 
s_ctl_fit(and(leave(P,L),open(P,'umbrella'))) --> 
                [P, 'left', 'the', L, 'and', 'she', 'opened', 'the', 'umbrella'],
                { female(P), fit(L,_) }.  

% CTL_NOFIT1: leave(apartment/restaurant) ∧ open(menu/mail) 

s_ctl_nofit1(and(leave(P,L),open(P,O))) --> 
                [P, 'left', 'the', L, 'and', 'he', 'opened', 'the', O],
                { male(P), nofit(L,O) }. 
s_ctl_nofit1(and(leave(P,L),open(P,O))) --> 
                [P, 'left', 'the', L, 'and', 'she', 'opened', 'the', O],
                { female(P), nofit(L,O) }.   

% CTL_NOFIT2: enter(restaurant/apartment) ∧ open(umbrella) 

s_ctl_nofit2(and(enter(P,L),open(P,'umbrella'))) --> 
                [P, 'entered', 'the', L, 'and', 'he', 'opened', 'the', 'umbrella'],
                { male(P), fit(L,_) }. 
s_ctl_nofit2(and(enter(P,L),open(P,'umbrella'))) --> 
                [P, 'entered', 'the', L, 'and', 'she', 'opened', 'the', 'umbrella'],
                { female(P), fit(L,_) }.
