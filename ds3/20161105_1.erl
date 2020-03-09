#!/usr/bin/env escript


new_process (Total, N) -> io:format("Process ~p\n", [N]).

%1 % process 0 firsts sends then receives
%1 new_process (Total, 0) -> done.
%1 
%1 % all other processes first receive then send.
%1 new_process (Total, N) -> 
%1     receieve {T,Sender} -> io:format("Process ~p received token ~p from process ~p.\n", N, T, Sender) end.

spawnN(Total, 0) -> [];
spawnN(Total, N) -> X = spawn(fun() -> new_process(Total, N) end),
                    Y = spawnN(Total, N-1),
                    [X|Y].

main(Args) -> [IP, OP] = Args,
               {ok, IF} = file:open(IP, [read]),
               {ok, OF} = file:open(OP, [write]),
               {ok, RawInput} = file:read(IF, 1024),
               [Nproc, Tok] = [list_to_integer(T) || 
                               T <- string:tokens(string:trim(RawInput), " ")],
               io:format("IP: ~p | OP: ~p | INPUT: ~p | Nproc: ~p | Tok: ~p\n", 
                         [IP, OP, RawInput, Nproc, Tok]),
               % spawn(fun() -> new_process() end),
               PIDs = spawnN(Nproc, Nproc),
               io:format("PIDs: ~p\n", [PIDs]),
               timer:sleep (1000),
               ok.

