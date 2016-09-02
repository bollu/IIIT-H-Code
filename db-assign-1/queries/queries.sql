1.


select title, ImdbRating from filmInfo natural join filmData natural join rating where ImdbRating > 6.0 order by ImdbRating desc
into outfile '1.txt' fields terminated by ',' lines terminated by '\n';

2.


select name from person natural join roles natural join filmData natural join filmInfo where Title = "The Hateful Eight"
order by name asc into outfile '2.txt' fields terminated by ',' lines terminated by '\n';

3.


select person.name as name from 
    person inner join roles on person.personId = roles.personId 
    inner join rolesMap on roles.role = rolesMap.roleId where 
    rolesMap.Name = "Director" or 
    rolesMap.name = "Actor" union
    select title as name from filminfo
    order by name asc
    into outfile '3.txt' fields terminated by ',' lines terminated by '\n';

4. 

select title from filmInfo where exists 
    (select * from roles actorRoles, rolesMap 
        where
        actorRoles.role = rolesMap.roleId and
        actorRoles.imdbId=filmInfo.imdbId and
        rolesMap.Name="Actor" and exists 
            (select * from roles directorRoles, rolesMap where
                directorRoles.role = rolesMap.roleId and
                directorRoles.imdbId=filmInfo.imdbId and
                rolesMap.Name = "Director" and
                directorRoles.personId = actorRoles.personId
                ))
    order by title
    into outfile '4.txt' fields terminated by ',' lines terminated by '\n';


5. 

select title, imdbrating  from 
    filmInfo natural join filmData natural join rating  where
    country="India" 
    order by imdbrating desc
    into outfile '5.txt' fields terminated by ',' lines terminated by '\n';


6.

select imdbRating from rating  where
    not exists 
    (select * from rating dup where 
        (dup.imdbId > rating.imdbId) and 
        (dup.imdbRating = rating.imdbRating)
        order by imdbId asc)
    order by imdbRating asc
    into outfile '6.txt' fields terminated by ',' lines terminated by '\n';

Notes:
======
files are stored in /usr/local/mysql/data/Movies/, so simply copy files fro this folder