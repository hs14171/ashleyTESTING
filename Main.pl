%% Main file with main ASHLEy functionality commands
%% adapted from Hoare.pl file
%% Harry Stern, 2017, for ASHLEy
%% Supervised by Oliver Ray

:- style_check(-discontiguous).
:- style_check(-singleton).
:- style_check(no_effect).

:-['Lexer.pl'].
:-['DCG.pl'].
:-['HoareLogic.pl'].
:-['Why.pl']. 
:-['WeakestPreconditions.pl'].
:-['Prove.pl'].
:-['Decode.pl'].


% generates T tabs
tabs(0) --> "".
tabs(T) --> {T1 is T-1}, "\t",tabs(T1).