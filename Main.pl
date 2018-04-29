%% Main file with main ASHLEy functionality commands
%% adapted from Hoare.pl file
%% Harry Stern, 2017, for ASHLEy
%% Supervised by Oliver Ray


:-['Lexer.pl'].
:-['DCG.pl'].
:-['HoareLogic.pl'].
:-['Why.pl'].
:-['WeakestPreconditions.pl'].
:-['Prove.pl'].
:-['Decode.pl'].
:-['ACSL.pl'].


% generates T tabs
tabs(0) --> "".
tabs(T) --> {T1 is T-1}, "\t",tabs(T1).