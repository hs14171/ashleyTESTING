%% File for reporting correctness of proofs or errors
%% adapted from Hoare.pl file
%% Harry Stern, 2017, for ASHLEy
%% Supervised by Oliver Ray


%% Need to get Alt-Ergo working by running: eval `opam config env`
check_file(File) :-
	lex_file(File,Tokens),
	syn(Tokens,[Pre,T,Post]),	
	goals(Pre,T,Post,Goals), % generate proof goals
	prove_goals(Goals),!.

check(Program) :-
	parse(Program, [Pre,T,Post]),
	goals(Pre,T,Post,Goals), % generate proof goals
	prove_goals(Goals),!.

prove_goals(Goals) :- !,
	GoalFile = "temp.why",
	write_goals(GoalFile,Goals),
	% run alt-ergo on the output file
	OutputFile = "temp.txt",
	concat("alt-ergo ",GoalFile, Cmd1), concat(Cmd1," >",Cmd2), concat(Cmd2,OutputFile,Cmd),
	shell(Cmd),
	read_file_lines(OutputFile,Output),
	check_results(Output,Results),
	ResultsFile = "results.txt",
	save_results(ResultsFile,Results,Goals).


%% Get the lines of a file
read_file_lines(File,Lines) :-
	open(File,read,Stream),
	read_lines(Stream,Lines),
	close(Stream),!.


read_lines(Stream,[L|Rest]) :- read_line_to_string(Stream,L), L\=end_of_file, read_lines(Stream,Rest).
read_lines(Stream,[]) :- read_line_to_string(Stream,end_of_file).


% Given the lines of alt-ergo output, check which have 
% been proven and which have not - 0 for no, 1 for yes
check_results([],[]).
check_results([Line|LRest], [0|PRest]) :- sub_string(Line,_,_,_,"I don't know"), check_results(LRest,PRest).
check_results([Line|LRest], [1|PRest]) :- sub_string(Line,_,_,_,"Valid"), check_results(LRest,PRest).


% Save the results to a file
save_results(File,Results,Goals) :-
	open(File,write,Stream),
	write_results(Stream,Results,Goals),
	close(Stream).

write_results(Stream,[],[]).
write_results(Stream,[R|Results],[[goal,Type,P1,P2,Text]|Goals]) :-
	atom_codes(M,Text),
	(
		(R=0, concat("Error trying to prove ",M, Line));
		(R=1, concat("Successfully proved ",M, Line))
	),
	write(Stream,Line), nl(Stream),
	writef(Line),nl,nl,
	write_results(Stream,Results,Goals).
write_results(Stream,Results,[[wp,W,S,Q]|Goals]) :- 
	decode(W,Pre), decode(S,Body), decode(Q,Post),
	writef("Calculated weakest precondition of:\n\t"),
	writef(Body),
	writef("\n\twith respect to postcondition:\n\t"),
	writef(Post), writef("\n\tis:\n\t"), writef(Pre),
	nl,nl,
	write_results(Stream,Results,Goals).




%%% Given a file annotated with (at least) postcondition and loop invariants, derives weakest preconditions and checks validity
%% prove_file(File) :-
%% 	% attempt to find a way to prove the program, otherwise return false and display message
%% 	(parse_file(File,S),
%% 		(
%% 			(S=[P,[F,T],Q],
%% 				wp(W,T,Q),!, decode(W,Wp),
%% 				display("Weakest preconditon for this program is:"),nl,
%% 				display(Wp),nl,
%% 				goals(P,pre(W,T),Q,G),
%% 				prove_goals(P,pre(W,T),Q,G)
%% 				);
%% 			(S=[F,post(T,Q)],
%% 				wp(W,T,Q),!,  decode(W,Wp),
%% 				display("Weakest preconditon for this program is:"), nl,
%% 				display(Wp), nl
%% 				)
%% 		),!
%% 	);
%% 	(display("Need to provide program postcondition."), false).


prove_file(File) :-
	parse_file(File,[P,[F,T],Q]),
	proof(P,[F,T],Q,G),
	prove_goals(G).


prove(Program) :-
	parse(Program,[P,[F,T],Q]),
	proof(P,[F,T],Q,G),
	prove_goals(G).







%% When proving, attempt to calculate weakest precondition and check equivalence/entailment, otherwise use hoare logic
	proof([P,T,Q],G) :- proof(P,T,Q,G).


	% simplest case, weakest preconditions can be found
	%% proof(P,[F,T],Q,[[goal,strengthen,W,P,M]]) :-
	%% 	wp(W,T,Q),
	%% 	decode(T,Program), decode(W,Pre),
	%% 	writef("Calculated weakest precondition of: "),nl,
	%% 	writef(Program),nl,
	%% 	writef("with respect to postcondition:"),nl,
	%% 	writef(Q), nl,
	%% 	writef(Pre), nl,
	%% 	goalMessage(strengthen,W,P,M),
	%% 	!.


	% otherwise use hoare logic:

	% empty statement
	% true if P is logically equivalent to P
	proof(P, [F,skip], Q, [[goal,skip,P,Q,M]]) :- goalMessage(skip,P,Q,M).

	% assignment
	proof(P, [F,assign(elem(X,I),E)],Q,[[goal,arraysubst,P,R,M]]) :- insert(Q,elem(X,I),E,R), goalMessage(arraysubst,P,elem(X,I),E,Q,M).

	% Prolog makes the subsitution, Alt-Ergo checks the 'up to 
	% normalization' step
	proof(P, [F,assign(X,E)], Q, [[goal,subst,P,R,M]]) :- subst(Q,X,E,R), goalMessage(subst,P,X,E,Q,M), \+X=elem(_,_).

	% sequence statement - here uses a seq_ functor which can also
	% hold the intermediate condition
	proof(P, [F,seq_(S1,R,S2)], Q, G) :-
		proof(P,[F,S1],R,G1),
		proof(R,[F,S2],Q,G2),
		append(G1,G2,G).

	% when a midcondition is not specified, calculate it using weakest preconditions
	proof(P,[F,seq(S1,S2)],Q,G) :-
		wp(R,S2,Q),
		%% writef("Computed weakest precondition of:\n"),
		%% decode(S2,M), writef(M),nl,
		%% writef("with respect to postcondition:"),
		%% decode(Q,Post), writef(Post), nl,
		%% writef("is:"), decode(R,Mid), writef(Mid),nl,
		proof(P,[F,S1],R,G1),
		proof(R,[F,S2],Q,G2),
		append(G1,[[wp,R,S2,Q]|G2],G).


	% conditional - either B holds and S1 is executed, or not(B)
	% and S2
	proof(P, [F,if(B,S1,S2)], Q, G) :-
		proof(and(P,B), [F,S1], Q, G1),
		proof(and(P,not(B)), [F,S2], Q, G2),
		append(G1,G2,G).



/* In the case of a while-loop while(E, S), the precondition of the
 * loop is per definition the invariant I of the loop and the
 * postcondition must be equivalent to and(I, not(E)). A subproof is
 * due for the body S of the loop such that the invariant follows as
 * postcondition of S for the precondition and(I, E), i.e., the
 * invariant and the loop's condition hold at the beginning of the
 * execution of the body.
 */
	proof(I, [F,while(B, S)], Q, [[goal,while,and(I,not(B)), Q, M] |G]) :-
		proof(and(I,B), [F,S], I, G), goalMessage(while,and(I,not(B)),Q,M).





% a procedure has the form [Name,[VariablesX, VariablesY],Tree]
% a call is made call(Name,Variables)

% if the called function s is in the list of procedures, then
% {P} call(s) {Q} holds if {P} T {Q} holds, where T is the tree representation of s

% rule for no variables passed:
	% Rule of Invocation:
	%% proc p ()() T, {P}T{Q} |- {P} call p () () {Q}
	proof(P,[F,call(S,[[],[]])],Q,G) :-
		\+recursive([S,[[],[]],T]),
		member([S,[[],[]],T],F),
		proof(P,[F,T],Q,G).


	proof(P,[Funcs,call(F,[X,Z])],Q,G) :-
		member([F,[X,Y],T],Funcs),
		varexp(Y,Z),
		proof(P,[Funcs,T],Q,G).


	% Rule of substitution
	%% {P} call p(x)(y) {R} |- {P(a/x,e/y)} call p(a)(e) {R(a/x,e/y)}
	% so from P call p(a)(e) {R}, need to work out what P' and R' were before substitution occurred
	proof(P_,[Funcs,call(F,[A,E])],Q_,G) :-
		member([F,[X,Y],T],Funcs),
		\+recursive([F,[X,Y],T]),
		varexp(A,B),
		subst(Pint,X,B,P_),
		subst(P,Y,E,Pint),
		subst(Qint,X,B,Q_),
		subst(Q,Y,E,Qint),
		varexp(Y,Z),
		% condition given in paper
		(
			( distinctlist(A), variables(int,E,V), intersection(V,A,[]));
			(display("Variables in first argument must be distinct and not appear in second arguments"),nl, abort)
		),

		proof(P,[Funcs,call(F,[X,Z])],Q,G).


	distinctlist([]).
	distinctlist([V|Vars]) :- \+member(V,Vars), distinctlist(Vars).

	% converts between x and variable(x)
	varexp(X,variable(X)) :- atomic(X), \+X=[].
	varexp([],[]).
	varexp([X|Vars],[V|Exps]) :- varexp(X,V), varexp(Vars,Exps).


	%% predicate for determining if a procedure is recursive
	recursive([F,_,T]) :- recursive(F,T).
	recursive(F,call(F,_)).
	recursive(F,seq_(T1,_,T2)) :- recursive(F,T1); recursive(F,T2).
	recursive(F,seq(T1,T2)) :- recursive(F,T1); recursive(F,T2).

	% rule of adaptation
	%% proof(P,[Funcs,call(F,[A,E])],Q,[[]]) :-
	%% 	member([F,[X,Y],T],Funcs),
	%% 	recursive([F,[X,Y],T]),


		





/* The precondition of a proof can be strengthened. While
 * simplification/normalization of assertions is performed
 * automatically, strengthening must be explicitly requested. (This is
 * well in line with the usual extra rule of Hoare logic for
 * strengthening the precondition.) In the following notation, we
 * assume pseudo syntax to express the precondition before
 * strengthening, whereas the precondition of the triple is the
 * strengthened one.
 */

	proof(Pre, [F,pre(Stronger, S)], Post, [[goal,strengthen,Pre,Stronger, M]|G]) :-
		proof(Stronger, [F,S], Post,G), goalMessage(strengthen, Pre, Stronger,M).

/* See strengthening of preconditions above. This rule is for
 * weakening of postconditions instead.
 */

 	% when weakening preconditions, need to prove Weaker -> post
	proof(Pre, [F,post(S,Weaker)], Post, H) :- proof(Pre, [F,S], Weaker, G), append(G,[[goal,weaken,Weaker,Post,M]],H), goalMessage(weaken,Weaker,Post,M).




% procedures and blocks
	proof(P,[Funcs,call(F,X,Y)],Q,G) :-
		member(proc(F,X,Y,T),Funcs),
		varexp(Y,Z),
		proof(P,[Funcs,T],Q,G).


% Rule of substitution
	%% {P} call p(x)(y) {R} |- {P(a/x,e/y)} call p(a)(e) {R(a/x,e/y)}
	% so from P call p(a)(e) {R}, need to work out what P' and R' were before substitution occurred
	proof(P_,[Funcs,call(F,A,E)],Q_,G) :-
		( 
		member(proc(F,X,Y,T),Funcs);
		(writef("Procedure "), display(F), writef(" not found\n"),abort)
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
			(writef("Variables in first argument must be distinct and not appear in second arguments\n"), abort)
		),
		proof(P,[Funcs,call(F,X,Y)],Q,G).


	proof(P,[F,block(V,S)],Q,G) :-
		% replace occurrences of x in S with a fresh variable
		length(V,N),
		freshVars(N,[P,[F,block(V,S)],Q],X),
		varexp(X,Vnew),
		subst(S,V,Vnew,T),
		
		proof(P,[F,T],Q,G).