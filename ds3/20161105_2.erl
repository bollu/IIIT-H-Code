#!/usr/bin/env escript
-import(lists,[nth/2]). 


main(Args) -> [IP, OP] = Args,
               {ok, IF} = file:open(IP, [read]),
               {ok, OF} = file:open(OP, [write]),
               {ok, RawInput} = file:read(IF, 1024),
               Input = [list_to_integer(T) || T <- string:tokens(string:trim(RawInput), " ")],
               io:format("IP: ~p | OP: ~p | INPUT: ~p\n", [IP, OP, Input]),
               ok.

