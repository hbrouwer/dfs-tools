:- use_module('../src/dfs_main.pl').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                              M O D E L                                %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%% Constants %%%%

@+ Person :- person(Person).
@+ Place  :- place(Place).
@+ Object :- object(Object).


%%%% Predicates %%%%

@* enter(Person,Place)  :- person(Person), place(Place).
@* leave(Person,Place)  :- person(Person), place(Place).
@* open(Person,Object)  :- person(Person), object(Object). 

%%%% Variables %%%%

female('francesca').
female('noortje').

male('harm').
male('matt').

person(P) :- female(P).
person(P) :- male(P).

place('restaurant').
place('apartment').

object('menu').
object('mail').
object('umbrella').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                       C O N S T R A I N T S                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% A person always enters or leaves a place
@# exists(y,or(enter(X,y),leave(X,y))) :- 
        person(X).

% A person never enters and leaves
@# neg(and(enter(X,Y),leave(X,Z))) :- 
        person(X), place(Y), place(Z).       

% A person enters only one place
@# imp(enter(X,Y),neg(exists(z,and(neg(z=Y),enter(X,z))))) :- 
        person(X), place(Y).

% A person leaves only one place
@# imp(leave(X,Y),neg(exists(z,and(neg(z=Y),leave(X,z))))) :- 
        person(X), place(Y).

% A person opens one and only one object
@# exists(y,open(X,y)) :- 
        person(X).
@# imp(open(X,Y),neg(exists(z,and(neg(z=Y),open(X,z))))) :- 
        person(X), object(Y).

% When entering, a person never opens a car door
% @# neg(and(enter(P,L),open(P,'car_door'))) :- 
%         person(P), place(L).

% When entering, a person never opens an umbrella        
% @# neg(and(enter(P,L),open(P,'umbrella'))) :- 
%         person(P), place(L).

% When leaving a restaurant, a person never opens mail      
% @# neg(and(leave(P,'restaurant'),open(P,'mail'))) :- 
        % person(P).

% When leaving an apartment, a person never opens a menu
% @# neg(and(leave(P,'apartment'),open(P,'menu'))) :- 
        % person(P).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                      P R O B A B I L I T I E S                        %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% enter(restaurant): menu > mail > umbrella
0.9 <- ( open(P,'menu')        | enter(P,'restaurant') ). 
0.9 <- ( enter(P,'restaurant') | open(P,'menu') ). 
0.3 <- ( open(P,'mail')        | enter(P,'restaurant') ). 
0.3 <- ( enter(P,'restaurant') | open(P,'mail') ). 
0.1 <- ( open(P,'umbrella')    | enter(P,'restaurant') ).
0.1 <- ( enter(P,'restaurant') | open(P,'umbrella') ).

% enter(apartment): mail > menu > umbrella
0.9 <- ( open(P,'mail')        | enter(P,'apartment') ). 
0.9 <- ( enter(P,'apartment')  | open(P,'mail') ). 
0.3 <- ( open(P,'menu')        | enter(P,'apartment') ). 
0.3 <- ( enter(P,'apartment')  | open(P,'menu') ). 
0.1 <- ( open(P,'umbrella')    | enter(P,'apartment') ).
0.1 <- ( enter(P,'apartment')  | open(P,'umbrella') ).

% leave(restaurant): umbrella > menu = mail
0.8 <- ( open(P,'umbrella')    | leave(P,'restaurant') ).
0.8 <- ( leave(P,'restaurant') | open(P,'umbrella') ).
0.3 <- ( open(P,'menu')        | leave(P,'restaurant') ).
0.3 <- ( leave(P,'restaurant') | open(P,'menu') ).
0.3 <- ( open(P,'mail')        | leave(P,'restaurant') ).
0.3 <- ( leave(P,'restaurant') | open(P,'mail') ).

% leave(apartment): umbrella > mail = menu
0.8 <- ( open(P,'umbrella')    | leave(P,'apartment') ).
0.8 <- ( leave(P,'apartment')  | open(P,'umbrella') ).
0.3 <- ( open(P,'mail')        | leave(P,'apartment') ).
0.3 <- ( leave(P,'apartment')  | open(P,'mail') ). 
0.3 <- ( open(P,'menu')        | leave(P,'apartment') ).
0.3 <- ( leave(P,'apartment')  | open(P,'menu') ).

0.5 <- ( _ | top ). % <- coin flip

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                           S E N T E N C E S                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% @~ enter(P,L) --> [P, 'entered', 'the', L], 
                %   { person(P), place(L) }.
% @~ leave(P,L) --> [P, 'left', 'the', L], 
                %   { person(P), place(L) }. 
% @~ open(P,O)  --> [P, 'opened', 'the', O], 
%                   { person(P), place(Object) }.
% @~ open(P,O)  --> ['he', 'opened', 'the', O], 
%                   { male(P), place(Object) }.
% @~ open(P,O)  --> ['she', 'opened', 'the', O], 
%                   { female(P), place(Object) }.

@~ (Sen,Sem) :- s(Sem,Sen,[]).
% @~ (Sen,Sem) :- s0(Sem,Sen,[]).
% @~ (Sen,Sem) :- s0(Sem,Sen,[]).
% @~ (Sen,Sem) :- s1(Sem,Sen,[]).

s(and(enter(P,L),open(P,O))) --> 
                [P, 'entered', 'the', L, 'and', 'he', 'opened', 'the', O],
                { male(P), place(L), object(O) }. 
s(and(enter(P,L),open(P,O))) --> 
                [P, 'entered', 'the', L, 'and', 'she', 'opened', 'the', O],
                { female(P), place(L), object(O) }.

s(and(leave(P,L),open(P,O))) --> 
                [P, 'left', 'the', L, 'and', 'he', 'opened', 'the', O],
                { male(P), place(L), object(O) }. 
s(and(leave(P,L),open(P,O))) --> 
                [P, 'left', 'the', L, 'and', 'she', 'opened', 'the', O],
                { female(P), place(L), object(O) }.                

% s0(and(enter(P,L),open(P,O))) --> 
%                 [P, 'entered', 'the', L, 'and', 'he', 'opened', 'the', O],
%                 { male(P), place(L), object_in(O) }. 
% s0(and(enter(P,L),open(P,O))) --> 
%                 [P, 'entered', 'the', L, 'and', 'she', 'opened', 'the', O],
%                 { female(P), place(L), object_in(O) }.
% 
% s0(and(leave(P,'restaurant'),open(P,'menu'))) --> 
%                 [P, 'left', 'the', 'restaurant', 'and', 'he', 'opened', 'the', 'menu'],
%                 { male(P) }.
% s0(and(leave(P,'restaurant'),open(P,'menu'))) --> 
%                 [P, 'left', 'the', 'restaurant', 'and', 'she', 'opened', 'the', 'menu'],
%                 { female(P) }.

% s0(and(leave(P,'apartment'),open(P,'mail'))) --> 
%                 [P, 'left', 'the', 'apartment', 'and', 'he', 'opened', 'the', 'mail'],
%                 { male(P) }.
% s0(and(leave(P,'apartment'),open(P,'mail'))) --> 
%                 [P, 'left', 'the', 'apartment', 'and', 'she', 'opened', 'the', 'mail'],
%                 { female(P) }.

% s1(and(leave(P,L),open(P,O))) --> 
%                 [P, 'left', 'the', L, 'and', 'he', 'opened', 'the', O],
%                 { male(P), place(L), object_out(O) }.
% s1(and(leave(P,L),open(P,O))) --> 
%                 [P, 'left', 'the', L, 'and', 'she', 'opened', 'the', O],
%                 { female(P), place(L), object_out(O) }.
