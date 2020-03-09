.PHONY: run
run: main.beam 
	erl -noshell -s main start -s init stop

main.beam: main.erl
	erlc main.erl
