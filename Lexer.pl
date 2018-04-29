%% %% DCG for the lexical analysis of While language
%% Harry Stern, 2017, for ASHLEy
%% Supervised by Oliver Ray

% When doing lexical analysis, add a newline \n at the end to close 
% any open comments

lex(Program, Tokens) :- concat(Program,"\n",Program_),atom_codes(Program_,P), phrase(tokens(Tokens),P).

lex_file(File,Tokens) :- read_file_to_string(File,Program,[]), lex(Program,Tokens).


% tokens generates a list of tokens from a program
tokens([]) --> "".
tokens(Rest) --> ignore, {!}, tokens(Rest).
tokens([T|Rest]) --> ((token(T), {!}) ; ([C], {writef("Lexical error, invalid character: "), writef([C]),nl, abort})), tokens(Rest).

%% Anything in 'ignore' does not generate a token
token --> ignore.


%%%%%%%%%%%%% Lexical terms of the language %%%%%%%%%%%
	token(implies) --> "->".
	token(semicolon) --> ";".
	token(assign) --> ":=".
	token(plus) --> "+".
	token(minus) --> "-".
	token(times) --> "*".
	token(openBracket) --> "(".
	token(closeBracket) --> ")".
	token(equals) --> "=".
	token(greaterthanorequal) --> ">=".
	token(lessthanorequal) --> "<=".
	token(greaterthan) --> ">".
	token(lessthan) --> "<".
	token(not) --> "!".
	token(and) --> "&".
	token(or) --> "||".
	token(openArray) --> "[".
	token(closeArray) --> "]".
	token(openAssertion) --> "{".
	token(closeAssertion) --> "}".
	token(comma) --> ",".
	token(colon) --> ":".



	token(skip) --> "skip".
	token(if) --> "if".
	token(then) --> "then".
	token(else) --> "else".
	token(while) --> "while".
	token(do) --> "do".
	token(true) --> "true".
	token(false) --> "false".

	token(procedure) --> "proc".
	token(call) --> "call".

	token(begin) --> "begin".
	token(end) --> "end".
	token(forall) --> "forall".
	token(exists) --> "exists".



	token(number(N)) --> digits(List), {catch(number_codes(N,List),_,false)}.

	digits([C|Rest]) --> [C], {is_digit(C), !}, digits(Rest).
	digits([]) --> [].


	% currently only alphabetical-only variables
	%% token(variable(X)) --> [C|Rest], {alphabetical([C|Rest]),atom_codes(X,[C|Rest]), \+phrase(keyword(X),_), \+phrase(symbol(X),_)}.
	token(variable(X))--> letters(List), {atom_codes(X,List)}.

	% true if given list is all alphabetical characters
	letters([C|Rest]) --> [C], {is_alpha(C)}, letters(Rest).
	letters([C])--> [C], {is_alpha(C)}.



%%%%%%%% Comments in the language %%%%%%


% elements of the language that should be ignored during tokenization
	ignore --> whitespace_ | comment.

	openComment --> "%".
	closeComment --> "\n".

	comment --> openComment, commentText, closeComment.
	commentText --> [C], {\+phrase(closeComment,[C]),!}, commentText | [].

	% at least one nonempty element of whitespace
	whitespace_ -->
		" ", {!}, whitespace
		|"\n", {!}, whitespace
		|"\t", {!}, whitespace.

	% whitespace is an arbitrary amount of whitespace
	whitespace -->
		" ", {!}, whitespace
		|"\n", {!}, whitespace
		|"\t", {!}, whitespace
		| [].


