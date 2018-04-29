%% %% Definite Clause Grammar for generating abstract syntax trees 
%% from the While language
%% Harry Stern, 2017, for ASHLEy
%% Supervised by Oliver Ray



:-use_module(library(readutil)).



syn(Tokens, Tree) :- (phrase(program(Tree),Tokens),!);
					((display("Syntactical error!"),nl,abort)).



parse(Program,Tree) :-
	lex(Program,Tokens),
	syn(Tokens,Tree).

parse_file(File,Tree) :- read_file_to_string(File,Program,[]), parse(Program,Tree).
parse_rule(bexp,Program,Tree) :- lex(Program,Tokens),!,
	phrase(bexp(Tree,_),Tokens).
parse_rule(Rule,Program,Tree) :- lex(Program,Tokens), phrase(call(Rule,Tree),Tokens).



% Rules for parsing a program in the While language, as specified by Oliver Ray.
% When removing left recursion, an underscore _ is used to specify the newly created rule, e.g. aexp and aexp_

% when assertions are included, returned tree is a list including 
% pre and post conditions
% and a list of procedures

% procedure declarations should be ignored
program([Pre,[Procs,T],Post]) --> procs(F), assertion(Pre), statements([G,T]), assertion(Post), procs(H), {union([F,G,H]
	,Procs)}.
program(T) --> statements(T).



optionalSemicolon --> [] | [semicolon].


statements(T) --> statement(T), optionalSemicolon.
statements([Procs,T]) --> statement([F1,S1]), [semicolon], assertion(P), statements([F2,S2]), optionalSemicolon, postcond(seq_(S1,P,S2),T), {union(F1,F2,Procs)}.
statements([Procs,T]) --> statement([F1,S1]), [semicolon], statements([F2,S2]), optionalSemicolon, postcond(seq(S1,S2),T), {union(F1,F2,Procs)}.



% preconditions can be strengthened before a statement or weakened after
statement([Procs,T]) --> assertion(Stronger), statement([Procs,S]), postcond(pre(Stronger,S),T).

statement([F,T]) --> procs(F), [skip], postcond(skip,T).
statement([F,T]) --> procs(F), [variable(X), assign], aexp(E), postcond(assign(X,E),T).
statement([F,T]) --> procs(F), [variable(X), openArray], aexp(I), [closeArray, assign], aexp(E), postcond(assign(elem(X,I),E),T).
statement([Procs,T]) --> procs(F), [if], bexp(B,program), [then], statement([F1,S1]), [else], statement([F2,S2]), postcond(if(B,S1,S2),T),{union([F1,F2,F],Procs)}.
statement([Procs,T]) --> procs(F), [while], bexp(B,program), [do], statement([G,S]), postcond(while(B,S),T), {union(F,G,Procs)}.
statement([F,T]) --> procs(F), [openBracket], statements([F,T]), [closeBracket].



% here, V should be the list of variables that are assigned in the body of F, and W is the list of other variables that occur in S
% as per Hoare

statement([[],T]) --> [call, variable(F), openBracket], procVars(A),[closeBracket,openBracket], procExps(E), [closeBracket], postcond(call(F,A,E),T).

statement([F,T]) --> [begin], procVars(V), statement([F,S]), [end], postcond(block(V,S),T).

% procedure declaration
procDec(proc(F,X,Y,S)) --> [procedure, variable(F), openBracket], procVars(X),
	[closeBracket, openBracket],
	procVars(Y), [closeBracket],
	statement([Procs,S]).

% procs stands for zero or more procedure declarations
procs([]) --> [].
procs([P|Procs]) --> procDec(P), [semicolon], procs(Procs).

procVars([]) --> [].
procVars([X|Rest]) --> [variable(X)], procVars_(Rest).

procVars_([]) --> [].
procVars_([X|Rest]) --> [comma, variable(X)], procVars_(Rest).

procExps([]) --> [].
procExps([E|Rest]) --> aexp(E), procExps_(Rest).

procExps_([]) --> [].
procExps_([E|Rest]) --> [comma], aexp(E), procExps_(Rest).





% eliminating left recursion for 'post' statements
% postconditions are added until the end of the statement is reached, at which point the correct tree is returned
postcond(S,post(T,W)) --> optionalSemicolon, assertion(W), postcond(S,T).
postcond(S,S) --> [].



assertion(B) --> [openAssertion], bexp(B,assertion), [closeAssertion].




%% Attempt to completely rewrite expressions with a single predicate and no left recursion

aexp(T) --> factor(E), aexp_(E,T).

aexp_(T,T) --> [].
aexp_(T1,T) --> [plus], factor(E), aexp_(add(T1,E),T).
aexp_(T1,T) --> [minus], factor(E), aexp_(sub(T1,E),T).

factor(T) --> term(E), factor_(E,T).

factor_(T,T) --> [].
factor_(T1,T) --> [times], term(E), factor_(mul(T1,E),T).

% aexp terminals
term(number(N)) --> [number(N)].
term(variable(X)) --> [variable(X)].
term(elem(X,E)) --> [variable(X), openArray], aexp(E),[closeArray].
term(E) --> [openBracket], aexp(E), [closeBracket].



bexp(T,A) --> bterm(B,A), bexp_(B,A,T).

bterm(true,_) --> [true].
bterm(false,_) --> [false].
bterm(B,A) --> [openBracket], bexp(B,A), [closeBracket].
bterm(eq(E1,E2),_) --> aexp(E1), [equals], aexp(E2).
bterm(geq(E1,E2),_)-->  aexp(E1), [greaterthanorequal], aexp(E2).
bterm(leq(E1,E2),_)-->  aexp(E1), [lessthanorequal], aexp(E2).
bterm(ge(E1,E2),_) --> aexp(E1), [greaterthan], aexp(E2).
bterm(le(E1,E2),_) --> aexp(E1), [lessthan], aexp(E2).
bterm(not(B),A) --> [not], bterm(B,A).
bterm(forall(V,B), assertion) --> [forall], procVars(V), bterm(B,assertion).
bterm(exists(V,B), assertion) --> [exists], procVars(V), bterm(B,assertion).

bexp_(T,_,T) --> [].
bexp_(T1,A,T) --> [and], bterm(T2,A), bexp_(and(T1,T2),A,T).
bexp_(T1,A,T) --> [or], bterm(T2,A), bexp_(or(T1,T2),A,T).
bexp_(T1,assertion,T) --> [implies], bterm(T2,A), bexp_(implies(T1,T2),A,T).





% V is the list of variables of type int/array occurring in an expression/program
% variable type can be specified in the first argument, otherwise returns all types of variables
variables([],[]).
variables([T|Rest],V) :- variables(T,V1), variables(Rest,V2), union(V1,V2,V).

variables(_,[],[]).
variables(Type,[T|Rest],V) :- variables(Type,T,V1), variables(Type,Rest,V2), union(V1,V2,V).

% atomics:
variables(skip,[]).
variables(number(_),[]).
variables(true,[]).
variables(false,[]).
variables(variable(X),[X]).
variables(elem(A,I),V) :- variables(I,V1), union(V1,[A],V).
variables(assign(elem(X,I),E),V) :- variables(I,V1), variables(E,V2), union([V1,V2,[X]],V),!.
variables(assign(X,E),V) :- variables(E,V1), union([X],V1,V),!.

variables(_,skip,[]).
variables(_,number(_),[]).
variables(_,true,[]).
variables(_,false,[]).

variables(int, variable(X),[X]).
variables(int, elem(A,I), V) :- variables(I,V).
variables(int, assign(elem(X,I),E),V) :- variables(int,I,V1), variables(int,E,V2), union(V1,V2,V),!.
variables(int, assign(X,E),V) :- variables(E,V1), union([X],V1,V),!.
variables(array, variable(_),[]).
variables(array, elem(A,I), V) :- variables(array,I,V1), union(V1,[A],V).
variables(array, assign(elem(X,I),E),V) :- variables(array,I,V1), variables(array,E,V2), union([V1,V2,[X]],V),!.
variables(array, assign(X,E),V) :- variables(E,V),!.




variables(if(B,S1,S2),V) :- variables(B,V1), variables(S1,V2), variables(S2,V2), union([V1,V2,V3],V).
variables(while(B,S),V) :- variables(B,V1), variables(S,V2), union(V1,V2).
variables(call(A,E),V) :- variables(E,V1), union(A,V1).
variables(proc(_,X,Y,S),V) :- variables(S,V1), union([X,Y,V1],V).
variables(block(X,S),V) :- variables(S,V1), union(V1,X,V).
variables(pre(P,S),V) :- variables(P,V1), variables(S,V2), union(V1,V2,V).
variables(post(S,Q),V) :- variables(S,V1), variables(Q,V2), union(V1,V2,V).

variables(Type,if(B,S1,S2),V) :- variables(Type,B,V1), variables(Type,S1,V2), variables(Type,S2,V2), union([V1,V2,V3],V).
variables(Type,while(B,S),V) :- variables(Type,B,V1), variables(Type,S,V2), union(V1,V2).
variables(Type,call(_,A,E),V) :- variables(Type,E,V1), union(A,V1).
variables(Type,proc(_,X,Y,S),V) :- variables(Type,S,V1), union([X,Y,V1],V).
variables(Type,pre(P,S),V) :- variables(Type,P,V1), variables(Type,S,V2), union(V1,V2,V).
variables(Type,post(S,Q),V) :- variables(Type,S,V1), variables(Type,Q,V2), union(V1,V2,V).


% for arithmetic/boolean expressions:
variables(not(B),V) :- variables(B,V).
variables(elem(A,I),V) :- variables(I,V1), union([A],V1,V).
variables(forall(X,B),V) :- variables(B,V1), subtract(V1,X,V).
variables(exists(X,B),V) :- variables(B,V1), subtract(V1,X,V).
variables(E,V) :-
	E =..[F,E1,E2], member(F,[eq,geq,leq,ge,le,add,mul,sub,and,or,implies]),
	variables(E1,V1), variables(E2,V2), union(V1,V2,V).



% for arithmetic/boolean expressions:
variables(Type, not(B),V) :- variables(Type,B,V).
variables(Type, forall(X,B),V) :- variables(Type, B,V1), delete(V1,X,V).
variables(Type, exists(X,B),V) :- variables(Type, B,V1), delete(V1,X,V).
variables(Type,E,V) :-
	E =..[F,E1,E2], member(F,[eq,geq,leq,ge,le,add,mul,sub,and,or,implies]),
	variables(Type,E1,V1), variables(Type,E2,V2), union(V1,V2,V).






% new predicate for union of multiple lists
% takes a list of lists as argument
union([],[]).
union([L|Lists],U) :- union(Lists,U1), union(L,U1,U).

intersection([],[]).
intersection([L|Lists],I) :- intersection(Lists,I1), intersection(L,I1,I).
