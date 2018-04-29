%% Definite Clause Grammar for generating readable programs/
%% formulae from abstract syntax
%% from the While language
%% Harry Stern, 2017, for ASHLEy
%% Supervised by Oliver Ray

decode(T,P) :- phrase(decode(T),C), atom_codes(P,C).


decode([P,T,Q]) --> token(openAssertion), decode(P), token(closeAssertion), "\n", decode(T), token(openAssertion), decode(Q), token(closeAssertion).


decode(seq(S1,S2)) --> decode(S1), token(semicolon),"\n", decode(S2).
decode(skip) --> token(skip).
decode(assign(elem(X,I),E)) --> decode(elem(X,I)), token(assign), decode(E), "\n".
decode(assign(X,E)) --> {atom_codes(X,C)}, C, token(assign), decode(E).
decode(if(B,S1,S2)) --> token(if), " ", decode(B), "\n", token(then),token(openBracket), "\n\t", decode(S1), token(closeBracket),"\n", token(else),"\n\t", token(openBracket), decode(S2), token(closeBracket).
decode(while(B,S)) --> token(while), " ", decode(B), " ", token(do), token(openBracket), "\n\t", decode(S), token(closeBracket).

decode(seq_(S1,R,S2)) --> decode(S1), token(semicolon), "\n", token(openAssertion), decode(R), token(closeAssertion), "\n", decode(S2).
decode(pre(B,S)) --> token(openAssertion), decode(B), token(closeAssertion), "\n", decode(S).
decode(post(S,B)) --> decode(S), "\n", token(openAssertion), decode(B), token(closeAssertion).

decode(add(T,E1)) --> decode(T), token(plus), decode(E1).
decode(sub(T,E1)) --> decode(T), token(minus), token(openBracket), decode(E1), token(closeBracket).
decode(mul(F,T1)) --> token(openBracket), decode(F), token(closeBracket), token(times), token(openBracket), decode(T1), token(closeBracket).

%% decode(number(N)) --> token(number(N)).
%% decode(variable(X)) --> token(variable(X)).
decode(number(N)) --> {atom_codes(N,C)}, C.
decode(variable(X)) --> {atom_codes(X,C)}, C.
decode(elem(X,I)) --> {atom_codes(X,[C|Rest])}, [C|Rest], token(openArray), decode(I), token(closeArray).

decode(and(B1,B2)) --> token(openBracket), decode(B1), " ", token(and), " ",decode(B2) , token(closeBracket).
decode(or(B1,B2)) --> token(openBracket), decode(B1), " ", token(or), " ", decode(B2) , token(closeBracket).
decode(implies(B1,B2)) --> token(openBracket), decode(B1), " ", token(implies), " ", decode(B2) , token(closeBracket).
decode(not(B)) --> token(not), " ", decode(B) .


decode(forall(V,B)) --> token(openBracket), token(forall)," ", decode(vars(V)), " ", token(openBracket), decode(B), token(closeBracket),token(closeBracket).
decode(exists(V,B)) --> token(openBracket), token(exists)," ", decode(vars(V)), " ", token(openBracket), decode(B), token(closeBracket),token(closeBracket).

decode(vars([])) --> "".
decode(vars([V|Vars])) --> decode(variable(V)), decode(vars_(Vars)).
decode(vars_([])) --> "".
decode(vars_([V|Vars])) --> token(comma), " ", decode(variable(V)), decode(vars_(Vars)).


decode(true) --> token(true).
decode(false) --> token(false).
decode(eq(E1,E2)) --> decode(E1), token(equals), decode(E2).
decode(geq(E1,E2)) --> decode(E1), token(greaterthanorequal), decode(E2).
decode(leq(E1,E2)) --> decode(E1), token(lessthanorequal), decode(E2).
decode(ge(E1,E2)) --> decode(E1), token(greaterthan), decode(E2).
decode(le(E1,E2)) --> decode(E1), token(lessthan), decode(E2).

