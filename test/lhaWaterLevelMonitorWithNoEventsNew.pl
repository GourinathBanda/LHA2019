go :-
	stateSpace(Xs1),
	rState(Xs1).


go :- location(L),
	probe(L,_).



bad(L0,T) :- badTransition(_Xs0,_Xs1,L0,T).
	
%--------------------------
% general transition system
%--------------------------

rState(Xs2) :-
	transition(Xs1,Xs2),  
	rState(Xs1).
rState(Ys) :-
	init(Xs),
	delayTransition(Xs,Ys).
	
%----------
% LHA model
%----------
%------------------------------------------
% transition remaining in the same location
%------------------------------------------
delayTransition(Xs0,Xs1) :-
	locationOf(Xs0,L0),
	before(Xs0,Xs1),
	d(Xs0,Xs1),			% rate of change constraint
	invariant(L0,Xs1).

%------------------------------------------
% transition from one location to another
%------------------------------------------
discreteTransition(Xs0,Xs3) :-
	locationOf(Xs0,L0),
	before(Xs0,Xs2),
	d(Xs0,Xs2),			% rate of change constraint
	gamma(T,L0,Xs2),		% transition constraint
	alpha(T,L0,Xs2,Xs3).		% action constraint


%------------------------------------------
% transition for transition system
%------------------------------------------

transition(Xs0,Xs2) :-
	discreteTransition(Xs0,Xs1),
	delayTransition(Xs1,Xs2).	% possible delay after

	
%------------------------------------------
% bad transition definition
%------------------------------------------
badTransition(Xs0,Xs1,L0,T) :-
	locationOf(Xs0,L0),
	invariant(L0,Xs0),
	d(Xs0,Xs1),			% rate of change constraint
	gamma(_T,L0,Xs1),		% transition constraint
	before(Xs2,Xs1),
	d(Xs0,Xs2),
	locationOf(Xs2,L0),
	negInvariant(L0,Xs2).
locationOf([Loc,_,_,_],Loc).

before([_,_,_,C],[_,_,_,F]) :-
	C=<F.


stateSpace([Loc,_,_,_]) :-
	location(Loc).


location(loc_0).

location(loc_1).

location(loc_2).

location(loc_3).

init([loc_0,+0,+1,0]).

invariant(loc_0,[loc_0,_,B,_]) :-
	B=<10.


negInvariant(loc_0,[loc_0,_,B,_]) :-
	B>10.


invariant(loc_1,[loc_1,A,_,_]) :-
	A=<2.


negInvariant(loc_1,[loc_1,A,_,_]) :-
	A>2.


invariant(loc_2,[loc_2,_,B,_]) :-
	B>=5.


negInvariant(loc_2,[loc_2,_,B,_]) :-
	B<5.


invariant(loc_3,[loc_3,A,_,_]) :-
	A=<2.


negInvariant(loc_3,[loc_3,A,_,_]) :-
	A>2.


d([loc_0,A,B,C],[_,D,E,F]) :-
	1*D=1*A+1*(F-C),
	1*E=1*B+1*(F-C).


d([loc_1,A,B,C],[_,D,E,F]) :-
	1*D=1*A+1*(F-C),
	1*E=1*B+1*(F-C).


d([loc_2,A,B,C],[_,D,E,F]) :-
	1*D=1*A+1*(F-C),
	1*E=1*B+ -2*(F-C).


d([loc_3,A,B,C],[_,D,E,F]) :-
	1*D=1*A+1*(F-C),
	1*E=1*B+ -2*(F-C).


gamma(0,loc_0,[loc_1,_,B,_]) :-
	B=10.


gamma(1,loc_1,[loc_2,A,_,_]) :-
	A=2.


gamma(2,loc_2,[loc_3,_,B,_]) :-
	B=5.


gamma(3,loc_3,[loc_0,A,_,_]) :-
	A=2.


alpha(0,loc_0,[loc_1,A,B,_],[loc_1,G,H,0]) :-
	G=0,
	H=B.


alpha(1,loc_1,[loc_2,A,B,_],[loc_2,G,H,0]) :-
	G=A,
	H=B.


alpha(2,loc_2,[loc_3,A,B,_],[loc_3,G,H,0]) :-
	G=0,
	H=B.


alpha(3,loc_3,[loc_0,A,B,_],[loc_0,G,H,0]) :-
	G=A,
	H=B.


