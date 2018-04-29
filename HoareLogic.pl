%% Rules for Hoare logic proof checking of programs in tree
%% structures as specified in Lexer and DCG
%% This version works out what goals need to be proven and outputs
%% them to a file to be input to Alt-Ergo
%% adapted from Hoare.pl file
%% Harry Stern, 2017, for ASHLEy
%% Supervised by Oliver Ray






parse_implies(P1,P2) :- parse_rule(bexp,P1,T1), parse_rule(bexp,P2,T2), implies(T1,T2).
%% parse_subst(B1,X,E,B2) :- parse_rule(bexp,B1,T1), parse_rule(aexp,E,T2), parse_rule(bexp,B2,T3), subst(T1,X,T2,T3).
parse_subst(E1,X,E2,T3) :- parse_rule(bexp,E1,T1), parse_rule(aexp,E2,T2), subst(T1,X,T2,T3).
parse_insert(P,Assignment,T) :- parse_rule(assertionLang,P,Cond), parse_rule(statement,Assignment,assign(elem(X,I),E)), insert(Cond, elem(X,I),E,T). 


parse_goals(Program,Goals) :- parse(Program,[P,T,Q]), goals(P,T,Q,Goals).
proof_file(File,Goals) :- parse_file(File,[P,T,Q]), goals(P,T,Q,Goals).



%% A goal takes the form of
%% [*goaltype*, predicate1, predicate2, *prettyprintedversion of 
%% goal*]
%% Types are: skip, subst, while, strengthen, weaken

write_program_goals_from_file(File,FileGoals,[P,T,Q]) :- parse_file(File,[P,T,Q]), goals(P,T,Q,Goals), write_goals(FileGoals,Goals).

write_program_goals(Program,File) :- parse_goals(Program,Goals), write_goals(File,Goals).
write_program_goals(P,Tree,Q,File) :- goals(P,Tree,Q,Goals), write_goals(File,Goals).


%%%%%%%% Substitution of variables in expressions %%%%%%%%%


	% Top-down traversal for substitution
	% subst(B1,X,E,B2) if B2 is B1 with every X replaced with E

	% rule for substituting in multiple variables at once
	subst(P,[],[],P).
	subst(P,[X|Vars],[E|Exps],Q) :- var(P), subst(P1,X,E,Q), subst(P,Vars,Exps,P1).
	%% subst(P,[X,Y],[A,E],Q) :- append(X,Y,Xy), append(A,E,Ae), subst(P,Xy,Ae,Q).
	subst(P,[X|Vars],[E|Exps],Q) :- var(Q), subst(P,X,E,Q1), subst(Q1,Vars,Exps,Q).

	% for reverse substitution, may need to bracket expressions!

	subst(elem(A,I),A,variable(B),elem(B,J)) :- subst(I,A,variable(B),J).
	subst(elem(A,I),X,E,elem(A,J)) :- subst(I,X,E,J), \+X==A.
	% if attempting to substitute an array for something other than a variable name, return an error
	subst(elem(A,I),A,B,elem(B,J)) :- display("Cannot substitute an array for an expression"), abort.

	subst(true,_,_,true).
	subst(false,_,_,false).
	subst(variable(X), X, E, E).
	subst(number(N), _, _, number(N)).
	subst(variable(X1), X2, _, variable(X1)) :-
		\+ X1 == X2.
	subst(add(E1,E2),X,A,add(F1,F2)) :- subst(E1,X,A,F1), subst(E2,X,A,F2).
	subst(sub(E1,E2),X,A,sub(F1,F2)) :- subst(E1,X,A,F1), subst(E2,X,A,F2).
	subst(mul(E1,E2),X,A,mul(F1,F2)) :- subst(E1,X,A,F1), subst(E2,X,A,F2).

	subst(eq(E1,E2),X,A,eq(F1,F2)) :- subst(E1,X,A,F1), subst(E2,X,A,F2).
	subst(geq(E1,E2),X,A,geq(F1,F2)) :- subst(E1,X,A,F1), subst(E2,X,A,F2).
	subst(leq(E1,E2),X,A,leq(F1,F2)) :- subst(E1,X,A,F1), subst(E2,X,A,F2).
	subst(ge(E1,E2),X,A,ge(F1,F2)) :- subst(E1,X,A,F1), subst(E2,X,A,F2).
	subst(le(E1,E2),X,A,le(F1,F2)) :- subst(E1,X,A,F1), subst(E2,X,A,F2).
	subst(not(E),X,A,not(F)) :- subst(E,X,A,F).
	subst(and(E1,E2),X,A,and(F1,F2)) :- subst(E1,X,A,F1), subst(E2,X,A,F2).
	subst(or(E1,E2),X,A,or(F1,F2)) :- subst(E1,X,A,F1), subst(E2,X,A,F2).
	subst(implies(E1,E2),X,A,implies(F1,F2)) :- subst(E1,X,A,F1), subst(E2,X,A,F2).

	subst(forall(X,B),X,_,forall(X,B)).
	subst(forall(X,B),Y,E,forall(X,B1)) :- subst(B,Y,E,B1), \+X==Y.
	subst(exists(X,B),X,_,forall(X,B)).
	subst(exists(X,B),Y,E,forall(X,B1)) :- subst(B,Y,E,B1), \+X==Y.

	subst(seq(S1,S2),X,E,seq(T1,T2)) :- subst(S1,X,E,T1),subst(S2,X,E,T2).
	subst(seq_(S1,R,S2),X,E,seq(T1,U,T2)) :- subst(S1,X,E,T1),subst(R,X,E,U), subst(S2,X,E,T2).
	subst(pre(P,S),X,E,pre(Q,T)) :- subst(P,X,E,Q),subst(S,X,E,T).
	subst(post(P,S),X,E,post(Q,T)) :- subst(P,X,E,Q),subst(S,X,E,T).
	subst(skip,_,_,skip).
	subst(assign(X,A),X,variable(Y),assign(Y,B)) :- subst(A,X,variable(Y),B),!.
	subst(assign(X,A),X,E,assign(X,B)) :- subst(A,X,E,B).
	subst(assign(X,A),Y,E,assign(X,B)) :- \+X==Y, subst(A,X,E,B).
	subst(if(A,S1,S2),X,E,if(B,T1,T2)) :- subst(A,X,E,B),subst(S1,X,E,T1), subst(S2,X,E,T2).
	subst(while(A,S),X,E,while(B,T)) :- subst(A,X,E,B),subst(S,X,E,T).


	%% subst(P,x,afdd(variable(y),number(1)),eq(add(variable(y),number(1)),number(2))).

	%% subst(E1, X, E0, E2) :-
	%% 	E1 =.. [F, E1a],
	%% 	E2 =.. [F, E2a],
	%% 	% Unary operators
	%% 	member(F, [not]),
	%% 	subst(E1a, X, E0, E2a).
	%% subst(E1, X, E0, E2) :-
	%% % Binary operators
	%% 	member(F, [eq, leq, geq, le, ge, add, sub, mul, and, or, implies]),
	%% 	E1 =.. [F, E1a, E1b],
	%% 	E2 =.. [F, E2a, E2b],
	%% 	subst(E1a, X, E0, E2a),
	%% 	subst(E1b, X, E0, E2b).

	


	


%% predicate for inserting array elements with top-down traversal
% insert(P,elem(x,i),e,Q) means Q is P with each element of a appearing x[i] evaluated as:
	% array x[i<-e][i] = e
	% array i!=j: x[i<-e][j] = x[i]

	insert(true,_,_,true).
	insert(false,_,_,false).
	insert(number(N),_,_,number(N)).
	insert(variable(X),_,_,variable(X)).
	insert(E1, X, E0, E2) :-
		E1 =.. [F, E1a],
		E2 =.. [F, E2a],
		% Unary operators
		member(F, [not]),
		insert(E1a,X,E0,E2a).
	insert(E1, X, E0, E2) :-
		E1 =.. [F, E1a, E1b],
		E2 =.. [F, E2a, E2b],
		% Binary operators
		member(F, [eq, leq, geq, le, ge, add, sub, mul, and, or, implies]),
		insert(E1a, X, E0, E2a),
		insert(E1b, X, E0, E2b).
	insert(forall(Y,E1),X,E0,forall(Y,E2)) :- insert(E1,X,E0,E2).

		% array x[i<-e][i] = e
		% array i!=j: x[i<-e][j] = x[i]

	% ( x[i<-e][j] corresponds to insert(elem(x,j),elem(x,i),e,_) )

	% if referring to different arrays, ignore
	insert(elem(X,I),elem(Y,_),_,elem(X,I)) :- \+X==Y.
	insert(elem(X,I),elem(X,I),E, E).
	insert(elem(X,I),elem(X,J),E,elem(X,I)) :- \+I==J.



	


%%%%%%%% Hoare logic rules %%%%%%%
	goals([P,T,Q],G) :- goals(P,T,Q,G).
	
	% empty statement
	% true if P is logically equivalent to P
	goals(P, [F,skip], Q, [[goal,skip,P,Q,M]]) :- goalMessage(skip,P,Q,M).

	% assignment
	goals(P, [F,assign(elem(X,I),E)],Q,[[goal,arraysubst,P,R,M]]) :- insert(Q,elem(X,I),E,R), goalMessage(arraysubst,P,elem(X,I),E,Q,M).

	% Prolog makes the subsitution, Alt-Ergo checks the 'up to 
	% normalization' step
	goals(P, [F,assign(X,E)], Q, [[goal,subst,P,R,M]]) :- subst(Q,X,E,R), goalMessage(subst,P,X,E,Q,M), \+X=elem(_,_).

	% sequence statement - here uses a seq_ functor which can also
	% hold the intermediate condition
	goals(P, [F,seq_(S1,R,S2)], Q, G) :-
		goals(P,[F,S1],R,G1),
		goals(R,[F,S2],Q,G2),
		append(G1,G2,G).

	% conditional - either B holds and S1 is executed, or not(B)
	% and S2
	goals(P, [F,if(B,S1,S2)], Q, G) :-
		goals(and(P,B), [F,S1], Q, G1),
		goals(and(P,not(B)), [F,S2], Q, G2),
		append(G1,G2,G).


	%% rule of declaration
	goals(P,[F,block(V,S)],Q,G) :-
		% replace occurrences of x in S with a fresh variable
		length(V,N),
		freshVars(N,[P,[F,block(V,S)],Q],X),
		varexp(X,Vnew),
		subst(S,V,Vnew,T),
		%% (
		%% 	(variables(P,V1), variables(Q,V2),
		%% 	intersection(V1,V,[]), intersection(V2,V,[]));
		%% 	(display("Variables in pre/postcondition cannot be declared in block"),nl,abort)
		%% ),
		goals(P,[F,T],Q,G).


	% returns a set of N new variables
	freshVars(0,_,[]):-!.
	freshVars(N,T,[V|Vars]) :- N1 is N-1, freshVars(N1,T,Vars), freshVar(T,V), \+member(V,Vars).
	
	% returns a completely new variable X
	freshVar(T,X) :- variables(T,V), varName(C), atom_codes(X,C), \+member(X,V).
	varName([C]) :- is_alpha(C),C>=97,C=<122.
	varName([V|C]) :- is_alpha(V), varName(C). 


/* In the case of a while-loop while(E, S), the precondition of the
 * loop is per definition the invariant I of the loop and the
 * postcondition must be equivalent to and(I, not(E)). A subproof is
 * due for the body S of the loop such that the invariant follows as
 * postcondition of S for the precondition and(I, E), i.e., the
 * invariant and the loop's condition hold at the beginning of the
 * execution of the body.
 */
	goals(I, [F,while(B, S)], Q, [[goal,while,and(I,not(B)), Q, M] |G]) :-
		goals(and(I,B), [F,S], I, G), goalMessage(while,and(I,not(B)),Q,M).



% a procedure has the form [Name,[VariablesX, VariablesY],Tree]
% a call is made call(Name,Variables)

% if the called function s is in the list of procedures, then
% {P} call(s) {Q} holds if {P} T {Q} holds, where T is the tree representation of s

% rule for no variables passed:

	%% proc p ()() T, {P}T{Q} |- {P} call p () () {Q}
	%% goals(P,[F,call(S,[[],[]])],Q,G) :-
	%% 	member([S,[],[],T],F),
	%% 	goals(P,[F,T],Q,G).

% Rule of Invocation:
	goals(P,[Funcs,call(F,X,Y)],Q,G) :-
		member(proc(F,X,Y,T),Funcs),
		varexp(Y,Z),
		goals(P,[Funcs,T],Q,G).


	% Rule of substitution
	%% {P} call p(x)(y) {R} |- {P(a/x,e/y)} call p(a)(e) {R(a/x,e/y)}
	% so from P call p(a)(e) {R}, need to work out what P' and R' were before substitution occurred
	goals(P_,[Funcs,call(F,A,E)],Q_,G) :-
		( 
		member(proc(F,X,Y,T),Funcs);
		(display("Procedure "), display(F), display(" not found"),nl,abort)
		),
		varexp(A,B),
		append(X,Y,Params),
		append(B,E,Args),
		subst(P,Params,Args,P_),
		subst(Q,Params,Args,Q_),
		%% varexp(Y,Z),
		% condition given in paper
		(
			( distinctlist(A), variables(E,V), intersection(V,A,[]));
			(display("Variables in first argument must be distinct and not appear in second arguments"),nl, abort)
		),
		goals(P,[Funcs,call(F,X,Y)],Q,G).


	distinctlist([]).
	distinctlist([V|Vars]) :- \+member(V,Vars), distinctlist(Vars).

	% converts between x and variable(x)
	varexp(X,variable(X)) :- atomic(X), \+X=[].
	varexp([],[]).
	varexp([X|Vars],[V|Exps]) :- varexp(X,V), varexp(Vars,Exps).




/* The precondition of a proof can be strengthened. While
 * simplification/normalization of assertions is performed
 * automatically, strengthening must be explicitly requested. (This is
 * well in line with the usual extra rule of Hoare logic for
 * strengthening the precondition.) In the following notation, we
 * assume pseudo syntax to express the precondition before
 * strengthening, whereas the precondition of the triple is the
 * strengthened one.
 */

	goals(Pre, [F,pre(Stronger, S)], Post, [[goal,strengthen,Pre,Stronger, M]|G]) :-
		goals(Stronger, [F,S], Post,G), goalMessage(strengthen, Pre, Stronger,M).

/* See strengthening of preconditions above. This rule is for
 * weakening of postconditions instead.
 */

 	% when weakening preconditions, need to prove Weaker -> post
	goals(Pre, [F,post(S,Weaker)], Post, H) :- goals(Pre, [F,S], Weaker, G), append(G,[[goal,weaken,Weaker,Post,M]],H), goalMessage(weaken,Weaker,Post,M).





%%% DCG for generating goal messages from goal objects

goalMessage(Type,P,Q,M) :- phrase(message(Type,P,Q),M),!.
goalMessage(Type,P,X,E,Q,M) :- phrase(message(Type,P,X,E,Q),M), !.
message(skip,P,Q) --> "skip statement: \n", decode(P), " is equivalent to\n", decode(Q).
message(arraysubst,P,X,E,Q) --> "array substitution: \n", decode(P), "\nis equivalent to \n", decode(Q), "\nwith ", decode(E), " inserted at ", decode(X).
message(subst,P,X,E,Q) --> "substitution:\n", decode(Q), "\nis equivalent to\n", decode(P), " with\n", decode(variable(X)), " substituted for ", decode(E).
message(while,and(I,not(B)),Q) --> "while loop: assertion\n", decode(I), "\nis invariant and\n", decode(and(I,not(B))), "\n is equivalent to \n", decode(Q).
message(strengthen,P,Q) --> "strengthened precondition:\n", decode(P), "\nimplies\n", decode(Q).
message(weaken,P,Q) --> "weakened postcondition: \n", decode(P), "\nimplies\n", decode(Q).

