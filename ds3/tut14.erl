-module(tut14).
% -export([main/1, main/2, main/0]).
-export([main/1]).


main() -> io:format("A0").
main(A1) -> io:format("A1: ~p\n", [A1]).
main(A1, A2) -> io:format("A1: ~p | A2: ~p\n", [A1, A2]).

