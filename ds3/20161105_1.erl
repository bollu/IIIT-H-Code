#!/usr/bin/env escript
-import(lists,[nth/2]). 


% new_process (Total, N) -> io:format("Process ~p\n", [N]).
new_process (Total, N) -> 
    % io:format("Process ~p spawned.\n", [N]),
    receive {OF, sendtok, P0, PIDs, Token, Sender} ->
        io:format(OF, "Process ~p received token ~p from process ~p.\n", [N, Token, Sender]),
        if N == Total-1 -> P0 ! {OF, sendtok, P0, PIDs, Token, N}; % final process send back to process 0
           true -> nth(N+1, PIDs) ! {OF,sendtok, P0, PIDs, Token, N} % non final process sends to 
        end
    end.

%1 % process 0 firsts sends then receives
%1 new_process (Total, 0) -> done.
%1 
%1 % all other processes first receive then send.
%1 new_process (Total, N) -> 
%1     receieve {T,Sender} -> io:format("Process ~p received token ~p from process ~p.\n", N, T, Sender) end.

spawnN(Total, N) -> 
    if Total == N -> [];
       true -> X = spawn(fun() -> new_process(Total, N) end),
                Y = spawnN(Total, N+1),
                [X|Y]
    end.

main(Args) -> [IP, OP] = Args,
               {ok, IF} = file:open(IP, [read]),
               {ok, OF} = file:open(OP, [write]),
               {ok, RawInput} = file:read(IF, 1024),
               [Nproc, Tok] = [list_to_integer(T) || 
                               T <- string:tokens(string:trim(RawInput), " ")],
               % io:format("IP: ~p | OP: ~p | INPUT: ~p | Nproc: ~p | Tok: ~p\n", [IP, OP, RawInput, Nproc, Tok]),
               % spawn(fun() -> new_process() end),
               PIDs = spawnN(Nproc, 1),
               [P1|_] = PIDs,
               P1 ! {OF, sendtok, self(), PIDs, Tok, 0},
               receive {OF, sendtok, _, PIDs, Token, Sender} ->
                io:format(OF, "Process 0 received token ~p from process ~p.\n", [Token, Sender])
               end,
               timer:sleep (10),
               ok.

