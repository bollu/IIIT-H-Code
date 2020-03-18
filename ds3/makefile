.PHONY: q1 q2 zip

q1:
	erlc 20161105_1.erl 
	erl -noshell -s 20161105_1 main q1in.txt q1out.txt -s init stop
	# escript 20161105_1.erl q1in.txt q1out.txt

q2:
	erlc 20161105_2.erl 
	erl -noshell -s 20161105_2 main q2in.txt q2out.txt -s init stop
	# escript 20161105_2.erl q2in.txt q2out.txt
zip:
	-rm -r 20161105/
	-rm 20161105.zip
	mkdir -p 20161105
	cp 20161105_1.erl 20161105_2.erl README.md 20161105
	zip 20161105.zip  -r 20161105
