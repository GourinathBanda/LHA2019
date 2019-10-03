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
