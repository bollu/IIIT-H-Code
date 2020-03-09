#!/usr/bin/env escript

new_process () ->
 io:format ("new_process\n"),
 exit ("Done").

main (_) ->
 spawn(fun() -> new_process() end),
 timer:sleep (100),
 ok.
