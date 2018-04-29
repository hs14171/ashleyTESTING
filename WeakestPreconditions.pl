%% Weakest preconditions for statements in While
%% Harry Stern, 2017, for ASHLEy
%% Supervised by Oliver Ray




parse_wp([P,Pre],Program,Post) :- parse(Program,T), parse_rule(bexp,Post,Q), wp(P,T,Q), decode(P,Pre).


% weakest precondition predicates are of the form wp(Pre,S,Post)

% weakest precondition of a skip statement is its postcondition
wp(P,skip,P).

% weakest precondition for assignment is the the same as
% postcondition but with occurences of varaible replaced with expression
wp(P,assign(elem(X,I),E),Q) :- insert(Q,elem(X,I),E,P), !.
wp(P,assign(X,E),Q) :- subst(Q,X,E,P).

% sequential statements, for both seq and seq_ structures
wp(P,seq(S1,S2),Q) :- wp(R,S2,Q), wp(P,S1,R).


% when a midcondition is given, ignore the second statement (ie assume R)
wp(P,seq_(S1,R,S2),Q) :- wp(P,S1,R).


wp(and(implies(B,P1),implies(not(B),P2)),if(B,S1,S2),Q) :-
	wp(P1,S1,Q), wp(P2,S2,Q).


%% guessed wp for block statements
wp(P,block(V,S),Q) :- wp(P,S,Q), variables(int,Q,V1), variables(array,Q,V2),
	(	(intersection(V,V1,[]), intersection(V,V2,[]));
		( display("Block variables appearing in block pre/postconditions."), abort)
	).


% for while statements, invariant must be provided
wp(P,pre(I,while(B,S)),Q) :- wlp(I,P,while(B,S),Q).
%% wp(P,seq_())
wp(P,while(_,_),_) :- writef("Loop invariant needs to be given for while loops\n"), abort.

wlp(I,and(I, and(implies(and(B, I), R), implies(and(not(B), I), Q) ) ),while(B,S),Q) :- wp(R,S,I).



% Given an unannotated program tree and postcondition, returns annotated tree

%% annotate([P,skip,Q],).
%% annotate([P,assign(X,E),Q],[P,assign(X,E),Q]) :- wp(P,assign(X,E),Q),!.
%% annotate([P,assign(X,E),Q],[P,pre(W,assign(X,E)),Q]) :- wp(W,assign(X,E),Q).

annotate_file(File) :-
	(parse_file(File,S),
		(
			(S=[P,[F,T],Q],
				annotate(T,Q,A), !,
				decode([P,A,Q],B),
				open("annotated.w",write,Stream),
				write(Stream,B),
				close(Stream)
				);
			(S=[F,post(T,Q)],
				annotate(T,Q,A), !,
				wp(W,T,Q),
				decode([W,A,Q],B),
				open("annotated.w",write,Stream),
				write(Stream,B),
				close(Stream)
				)
		),!
	);
	(display("Need to provide program postcondition."), abort).


% annotate (S,Q,T) means T is S with relevant midconditions inserted


annotate(skip,Q,skip).
annotate(assign(X,E),Q, assign(X,E)).


% interpret a midcondition before a while loop as an invariant
%% annotate(seq_(S1,I,while(B,S2)),Q,T) :- annotate(seq(S1,pre(I,while(B,S2))),Q,T).
annotate(seq(S1,S2),Q,seq_(T1,R,T2)) :- wp(R,S2,Q), annotate(S1,R,T1), annotate(S2,Q,T2).
annotate(seq_(S1,R,S2),Q,seq_(T1,R,T2)) :- annotate(S1,R,T1), annotate(S2,Q,T2).

annotate(if(B,S1,S2),Q,if(B,pre(P1,T1),pre(P2,T2))) :-
	wp(and(implies(_,P1),implies(_,P2)),if(B,S1,S2),Q),
	annotate(S1,Q,T1), annotate(S2,Q,T2).

% for a while loop, invariant needs to be given beforehand
% after the loop, need to insert condition that loop condition is now false
annotate(pre(I,while(B,S)),Q,post(pre(I,while(B,pre(W,T))),and(not(B),I))) :-
	annotate(S,I,T), wp(W,S,I).


annotate(block(V,S),Q, block(V,T)) :- annotate(S,Q,T).


% with a pre() statement, if the strengthened precondition is not equal the to the weakest precondition, it needs to be strengthened
annotate(pre(P,S),Q,pre(P,T)) :- annotate(S,Q,T), wp(P,S,Q).
annotate(pre(P,S),Q,pre(P,pre(W,T))) :- annotate(S,Q,T), wp(W,S,Q),\+P==W.

annotate(post(S,Q),Q,T) :- annotate(S,Q,T).
annotate(post(S,Q),R,post(T,Q)) :- annotate(S,Q,T).




write_program_to_file(T,File) :- open(File,write,Stream), decode(T,P), write(Stream,P), close(Stream).