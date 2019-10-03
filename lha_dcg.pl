:- module(lha_dcg,_).

%:- use_module(library(atom2term)).
:- use_module(library(lists)).
:- use_module(library(read_from_string), [read_from_atom/2]).

:- use_module(lhaGenSpec).

:- op(600, xfx, ':=').
%% :- op(600, fx, 'rate').


main(Tree,X,S1,ToBeGeneratedOutputFileName) :- 
	lha(Tree,X,[]),
	!,
	write('parsing completed'),nl,
	write('The parse tree is:'),nl,
	write(Tree),nl,
	open('output.tree',write,TreeStream),
	writeTree(TreeStream,Tree),
	close(TreeStream),	
	genSpec(Tree,S1),
	write('ExecutedS1'),
	open(ToBeGeneratedOutputFileName,write,Stream),
	writePrologPredicates(S1,Stream),
	close(Stream).

writeTree(Stream,lha(VarList,LocationList,TransitionList)) :-
	writePrologPredicates(VarList,Stream),
	writePrologPredicates(LocationList,Stream),
	writePrologPredicates(TransitionList,Stream).


writePrologPredicates([R|Rs],S) :-
	R \= (_H :- _B),
	write(S,R),
	write(S,'.'), 
	nl(S),
	nl(S),
	writePrologPredicates(Rs,S).


writePrologPredicates([],_).
writePrologPredicates([R|Rs],S) :-
	R = (H :- B),
	write(S,H),
	write(S,' :-'), nl(S),
	writeBody(B,S),
	nl(S),
	writePrologPredicates(Rs,S).

writeBody(C,S) :-
	C \= (_X','_Y),
	write(S,'\t'),
	write(S,C),
	write(S,'.'),
	nl(S),
	nl(S).

writeBody((C1','B),S) :-
	write(S,'\t'),
	write(S,C1),
	write(S,','),
	nl(S),
	writeBody(B,S).




/*
main(List,Predicates) :-
	open('fileOut.pl',write,S),
	writePrologPredicates(List,S, Predicates),
	close(S).
	

writePrologPredicates([],_,[]).
writePrologPredicates([R|Rs],S,[R,'$VAR'('.')|Predicates]) :-
	write(S,R),
	write(S,'.'),
	nl(S),	
	nl(S),
	writePrologPredicates(Rs,S,Predicates).

*/

/*
test(Tree,S) :- main(Tree,[
('variable',9),
('(',14),
('numeric',5),
(',',16),
('t',24),
(')',15),
('.',18),

('variable',9),
('(',14),
('bool',5),
(',',16),
('b',24),
(')',15),
('.',17),

('location',12),
('(',14),
('loc_0',23),
(',',16),
('(',14),
('rate',10),
('(',14),
('t',24),
(',',16),
('1',21),
(')',15),
(')',15),
(',',16),
('(',14),
('t',24),
('+',19),
('1',21),
('<',20),
('-',19),
('10',21),
('&',_),
('t',_),
('>',_),
('8',_),
(')',15),
(')',15),
('.',17),
('init',11),
('(',14),
('loc_0',23),
(',',16),
('(',14),
('t',24),
(':=',31),
('0',21),
(')',15),
(')',15),
('.',17),
('transition',13),
('(',14),
('(',14),
('loc_0',23),
(',',16),
('loc_0',23),
(')',15),
(',',16),
('(',14),
('t',24),
('==',20),
('10',21),
(')',15),
(',',16),
('(',14),
('t',24),
(':=',31),
('0',21),
(')',15),
(')',15),
('.',17)],S).
*/


/* test(Tree,S) :- main(Tree,[
('variable',9),
('(',14),
('numeric',5),
(',',16),
('t',24),
(')',15),
('.',17),
('location',12),
('(',14),
('loc_0',23),
(',',16),
('(',14),
('rate',10),
('(',14),
('t',24),
(',',16),
('1',21),
(')',15),
(')',15),
(',',16),
('(',14),
('t',24),
('+',19),
('1',21),
('<',20),
('10',21),
(')',15),
(')',15),
('.',17),
('init',11),
('(',14),
('loc_0',23),
(',',16),
('(',14),
('t',24),
(':=',31),
('0',21),
(')',15),
(')',15),
('.',17),
('transition',13),
('(',14),
('(',14),
('loc_0',23),
(',',16),
('loc_0',23),
(')',15),
(',',16),
('(',14),
('t',24),
('==',20),
('10',21),
(')',15),
(',',16),
('(',14),
('t',24),
(':=',31),
('0',21),
(')',15),
(')',15),
('.',17)],S).

*/

main([InFile,OutFile]) :-
	test(InFile,_,_,OutFile).

test(TokenizedInputLhaSpecFileName,Tree,S,ToBeGeneratedOutputFileName) :- 
	open(TokenizedInputLhaSpecFileName,read,ParsedInputLha),
	write('opened read stream'),nl,
	read(ParsedInputLha,ParsedInputLhaAsList),
	write('reading the stream succeeded'),nl,
	last(ParsedInputLhaAsList,EmptySpace),
	write('trimmed off the empty token'),nl,
	append(InputLha,[EmptySpace],ParsedInputLhaAsList),
	write('InputLha is:'),nl,
	write(InputLha),nl,
	write('append succeeded'),nl,
	main(Tree,InputLha,S,ToBeGeneratedOutputFileName),
	write('call to main terminated with success'),nl,
	write('***** Compilation Success *****'),nl.



lha(lha(A,B,C)) -->
  variabledeclaration_plus(A), {write('parsed declarations'),nl},
  location_plus(B), {write('parsed locations'),nl},
  transition_plus(C), {write('parsed transitions'),nl}.
 

variabledeclaration_plus([V|Vs]) --> 
	{write('variable declarations reached'),nl},
	variabledeclaration(V),
	{write('variable declarations first time'),nl},
	variabledeclaration_plus(Vs).

variabledeclaration_plus([Vs]) --> 
	variabledeclaration(Vs),
	{write('variable declarations finished'),nl}.


variabledeclaration(vardecl(T,I))  -->
	{write('variable declaration once called'),nl},
	variable(_), lbrace, typeToken(T), comma, identifier(I), rbrace, fullstop,
	{write('variable declaration once succeeded'),nl}.


location_plus([L|Ls]) --> 
	location(L),
	location_plus(Ls).

location_plus([Ls]) --> 
	location(Ls).


location(locdecl(Li,Dt,It)) -->
    locationToken, lbrace, 
    locationId(Li), comma, 
    derivativestuple(Dt), comma,
    invariantstuple(It),
    rbrace, fullstop.


transition_plus([T|Ts]) --> 
	transition(T),
	transition_plus(Ts).

transition_plus([T]) --> 
	transition(T).

transition(I) -->
	initialization(I).

transition(D) -->
	discretetransition(D).


initialization(init(Li,At))  -->
	init, lbrace, locationId(Li), comma, actionstuple(At), rbrace, fullstop.

/*changed 7:08 PM d- 6 Nov 2007 ************
discretetransition([transition(Lp,Gt,At)]) -->
	transitionToken, lbrace,  
	locationsPair(Lp), comma, 
	guardstuple(Gt), comma, 
	actionstuple(At), 
	rbrace, fullstop.
*changed 7:08 PM d- 6 Nov 2007 ************/

discretetransition(transition(Lp,Gt,At)) -->
	transitionToken, lbrace,  
	locationsPair(Lp), comma, 
	guardstuple(Gt), comma, 
	actionstuple(At), 
	rbrace, fullstop.

derivativestuple(Ds) -->
	lbrace, derivatives(Ds), rbrace.


derivatives([D|Ds]) -->
	derivative(D), derivative_cont(Ds).


derivative_cont([D|Ds]) -->
	comma, derivative(D),
	derivative_cont(Ds).

derivative_cont([]) --> [].


/**** 11:58 AM Nov 8 2007 ****
derivative(derivative(D)) -->
	rate(R), lbrace, identifier(I), comma, constant(C), rbrace, { D =.. [R,ident(I),C]}.
**** 11:58 AM Nov 8 2007 ****/

%% { replaced by 11:58 AM Nov 8 2007 ****
/*** replace *** BEGINS *** on 14:19 PM Jan 17 2008 ****
derivative(derivative(D)) -->
	rate(R), lbrace, identifier(I), rbrace, rateRelation(Rr),  constant(C),  
	{ Rate =.. [R,ident(I)] , D =.. [Rr,Rate,C]}.
**** replace *** ENDS *** on 14:19 PM Jan 17 2008 ****/
%% replacement ends by 11:58 AM Nov 8 2007 ****}

%% {**** replaced by **** added on 14:19 PM Jan 17 2008 ****/
derivative(derivative(D)) -->
	rate(R), lbrace, identifier(I), rbrace, rateRelation(Rr),  expression(E),  
	{ Rate =.. [R,ident(I)] , D =.. [Rr,Rate,E]}.
%% {**** replaced by **** added on 14:19 PM Jan 17 2008 ****/


%% [derivative(rate(ident(x),num(+1))),derivative(rate(ident(w),num(+1)))]

constant(num(T)) --> 
	sign_opt(S), decimalnumber(Dn), {T =.. [S,Dn]}.

constant(num(T)) --> 
	sign_opt(S), number(N), {T =.. [S,N]}.

invariantstuple(Is) -->
	lbrace, invariants(Is), rbrace.


invariants(Is) -->
	invariant(I), invariant_cont(Is1),
	{formExpr(I,Is1,Is)}.


invariant_cont([Ao,E]) -->
	andor(Ao), invariant(I),
	invariant_cont(Is),
	{formExpr(I,Is,E)}.

invariant_cont([]) --> [].

invariant(invariant(I)) --> 
	expression(E), binaryRelation(Br), sign_opt(S), number(N),
	{Sn =.. [S,N], I =.. [Br,E,num(Sn)]}.

invariant(invariant(I)) --> 
	expression(E1), binaryRelation(Br), expression(E2),
	{I =.. [Br,E1,E2]}.

expression(Ae) --> 
	additiveexpression(Ae).


additiveexpression(E) --> 
	multiplicativeexpression(Me), multiplicativeexpression_cont(Mes), 
	{formExpr(Me,Mes,E)}.


multiplicativeexpression_cont([S,E]) -->
	sign(S), multiplicativeexpression(Me), 
	%{ Me = [X], MExp =.. [S,X]},
	multiplicativeexpression_cont(Mes),
	{formExpr(Me,Mes,E)}.

multiplicativeexpression_cont([]) --> [].

multiplicativeexpression(E) --> 
	unaryexpression(Ue), unaryexpression_cont(Ues),
	{formExpr(Ue,Ues,E)}.


unaryexpression_cont([Eo,E]) --> 
	expressOp(Eo), unaryexpression(Ue), 
	% {Exp =.. [Eo,Ue]},
	unaryexpression_cont(Ues),
	{formExpr(Ue,Ues,E)}.

unaryexpression_cont([]) --> [].
	
formExpr(E,[],E).
formExpr(E,[Op,E1],E2) :-
	E2 =.. [Op,E,E1].

%% unaryexpression(Ue) --> 
%%	lbrace, expression(Ue), rbrace.

unaryexpression(Ue) --> 
	lbrace, expression(Ue), rbrace.

unaryexpression(ident(I)) --> 
	identifier(I).
unaryexpression(num(T)) --> 
	sign_opt(S), decimalnumber(Dn), {T =.. [S,Dn]}.
unaryexpression(num(T)) --> 
	sign_opt(S), number(N), {T =.. [S,N]}.

locationsPair(locpair(Li1,Li2)) -->
	lbrace, locationId(Li1), comma, locationId(Li2), rbrace.

/* 

actionstuple(As) -->
	lbrace, actions(As), rbrace.


actions([]) --> [].
actions([A|As]) -->
	action(A), action_cont(As).

action_cont([A|As]) -->
	comma, action(A),
	action_cont(As).

action_cont([]) --> [].

action(action(A)) -->
	identifier(I), assignOp(Ao), sign_opt(So),decimalnumber(Dn),
	{Sdn =.. [So,Dn], A =.. [Ao,ident(I),num(Sdn)]}.
action(action(A)) -->
	identifier(I), assignOp(Ao), number(N), 
	sign_opt(So), {Sn =.. [So,N], A =.. [Ao,ident(I),num(Sn)]}.

*/


guardstuple(Gs) -->
	lbrace, guards(Gs), rbrace.

guards([G|Gs]) -->
	guard(G), guard_cont(Gs).

guard_cont([G|Gs]) -->
	comma, guard(G),
	guard_cont(Gs).

guard_cont([]) --> 
	[].



/***  replaced for changing the pattern of guards with eliminated AND/OR inter-weaving **** Nov 28 2007 11:32AM **********

guard_cont([(Ao,G)|Gs]) -->
	andor(Ao), guard(G),
	guard_cont(Gs).

**** Nov 28 2007 11:32 AM ***replacement ends*******/

guard(G) --> 
	expression(E1), binaryRelation(Br), expression(E2),
	{G =.. [Br,E1,E2]}.

sign_opt('+') --> 
	[].
sign_opt(S) --> 
	sign(S).

/*
actionstuple(As) -->
	lbrace, actions(As), rbrace.


actions([A|As]) -->
	action(A), action_cont(As).

action_cont([]) --> 
	[].
*/

/*****Nov-07-2007,12:23 PM ***** 
action_cont([',',E]) --> 
	comma, action(A),
	action_cont(As),
	{formExpr(A,As,E)}.
******Nov-07-2007,12:23 PM *****/

/*
%% replacement by:Nov-07-2007,12:23 PM begins

action_cont([E]) --> 
	comma, action(A),
	action_cont(As),
	{formExpr(A,As,E)}.

%% replacement by:Nov-07-2007,12:23 PM end


action(action(A)) -->
	identifier(I), assignOp(Ao), sign_opt(So), 
	decimalnumber(Dn), {Sdn =.. [So,Dn], A =.. [Ao,ident(I),num(Sdn)]}.
action(action(A)) -->
	identifier(I), assignOp(Ao), number(N), 
	sign_opt(So), {Sn =.. [So,N], A =.. [Ao,ident(I),num(Sn)]}.

*/


actionstuple(As) -->
	lbrace, actions(As), rbrace.


actions([]) --> [].
actions([A|As]) -->
	action(A), action_cont(As).

action_cont([A|As]) -->
	comma, action(A),
	action_cont(As).

action_cont([]) --> [].

action(action(A)) --> 
	expression(E1), assignOp(Ao), expression(E2),
	{A =.. [Ao,E1,E2]}.

action(action(A)) --> 
	expression(E1), actionRelation(Ao), expression(E2),
	{A =.. [Ao,E1,E2]}.

/*
action(action(A)) -->
	identifier(I), assignOp(Ao), sign_opt(So),decimalnumber(Dn),
	{Sdn =.. [So,Dn], A =.. [Ao,ident(I),num(Sdn)]}.

action(action(A)) -->
	identifier(I), assignOp(Ao), number(N), 
	sign_opt(So), {Sn =.. [So,N], A =.. [Ao,ident(I),num(Sn)]}.
*/

assignOp(':=') --> [(':=',_)].

lbrace --> [('(',_)].
rbrace --> [(')',_)].

fullstop --> [('.',17)].

andor(and) --> [('&',_)].
andor(or) --> [('|',_)].


locationId(L) --> [(L,25)].
identifier(X) --> [(X,26)].

transitionToken --> [('transition',_)].
locationToken --> [('location',_)].

init --> [('init',_)].

binaryRelation('>=') --> [('>=',_)].
binaryRelation('>') --> [('>',_)].
binaryRelation('=<') --> [('=<',_)].
binaryRelation('<') --> [('<',_)].
binaryRelation('==') --> [('==',_)].


rateRelation('>=') --> [('>=',_)].
rateRelation('>') --> [('>',_)].
rateRelation('=<') --> [('=<',_)].
rateRelation('<') --> [('<',_)].
rateRelation('=') --> [('=',_)].

actionRelation(X) --> rateRelation(X).

number(M) --> [(N,23)], {read_from_atom(N,M)}.
decimalnumber(M) --> [(Dn,24)], {read_from_atom(Dn,M)}.


%% type --> [('numeric',_),('bool',_),('enumerated',_)].

typeToken('numeric') --> [('numeric',_)].
typeToken('bool') --> [('bool',_)].
typeToken('enumerated') --> [('enumerated',_)].

comma --> [(',',_)].

rate('rate') --> [('rate',_)].
variable('variable') --> [('variable',_)].

sign('+') --> [('+',_)].
sign('-') --> [('-',_)].

expressOp('*') --> [('*',_)].
expressOp('/') --> [('/',_)].
expressOp('mod') --> [('%',_)].
