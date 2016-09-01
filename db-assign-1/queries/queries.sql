1.


select title, ImdbRating from filmInfo natural join filmData natural join rating where ImdbRating > 6.0 order by ImdbRating desc
into outfile '1.txt' fields terminated by ',' lines terminated by '\n';

2.


select name from person natural join roles natural join filmData natural join filmInfo where Title = "The Hateful Eight"
order by name asc into outfile '2.txt' fields terminated by ',' lines terminated by '\n';;

Notes:
======
files are stored in /usr/local/mysql/data/Movies/, so simply copy files fro this folder