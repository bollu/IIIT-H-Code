#!/usr/bin/env escript
-import(lists,[nth/2, split/2]). 

% merge operation.
mergelist(XS, []) -> XS;
mergelist([], YS) -> YS;
mergelist([X|XS], [Y|YS]) -> 
        if X < Y -> [X|mergelist(XS, [Y|YS])];
           true -> [Y|mergelist([X|XS], YS)]
        end.
            


% sort operation.
sortlist(PidParent, []) -> 
  io:format("1. ~p <- ~p | XS: ~p\n", [self(), PidParent, []]),
  PidParent ! {[]};
sortlist(PidParent, [X]) -> 
  io:format("2. ~p <- ~p | XS: ~p\n", [self(), PidParent, [X]]),
  PidParent ! {[X]};
sortlist(PidParent, [X, Y]) -> 
  io:format("3. ~p <- ~p | XS: ~p\n", [self(), PidParent, [X, Y]]),
  if X < Y ->  PidParent ! {[X, Y]}; 
     true -> PidParent ! {[Y, X]}
  end;
sortlist(PidParent, XS) -> 
  Self = self(),
  % io:format("4. ~p <- ~p | XS: ~p\n", [Self, PidParent, XS]),
  {L, R} = split(length(XS) div 2, XS), 
  LPid = spawn(fun() -> sortlist(Self, L) end),
  RPid = spawn(fun() -> sortlist(Self, R) end),
  io:format("4. ~p -> [~p, ~p]\n", [Self, LPid, RPid]),
  receive  {XS1} -> 
      receive {XS2} -> 
          io:format("5. ~p <- [~p , ~p] (~p, ~p)\n", [Self, LPid, RPid, XS1, XS2]),
          PidParent ! {mergelist(XS1, XS2)}
      end
  end.

main(Args) -> [IP, OP] = Args,
               {ok, IF} = file:open(IP, [read]),
               {ok, OF} = file:open(OP, [write]),
               {ok, RawInput} = file:read(IF, 1024),
               Input = [list_to_integer(T) || T <- string:tokens(string:trim(RawInput), " ")],
               Self = self(),
               io:format("IP: ~p | OP: ~p | INPUT: ~p | Self: ~p \n", [IP, OP, Input, Self]),
               sortlist(Self, Input),
               receive {Sorted} -> 
                   io:format(OF, "~p", [Sorted]),
                   ok
                end.

