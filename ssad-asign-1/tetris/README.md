Keymap
======
'a': move left
'd': move right
's': fall block fully at current position
'j': rotate clockwise
'k': rotate CCW
'q': quit

Block Appearances
=================

'ooo': Standard Block
'***': destroys anything in a 1 block radius of the shape of the block

Scoring
=======

Block added: 50 points
Row cleared: 1000 points

Architecture
============

The game uses a MVC architecture, with

Model: `Board` class
View: `View` interfacte with concrete `CLIView` class
Controller: the `Game` class which knits together the model and the View


The one (non-standard) thing is that there is both a `Shape` class and a `Block` class.
While this might seem counter-intuitive at first glance, It's actually really neat.

A lot of things in tetris, such as
  - figuring out where to place blocks
  - checking if a row is filled
  - moving the block downwards and then applying collision detection

all only require the geometric information of the block, and not the block
itself. So, I separate the concept of a "Shape" from a "Block"
(a Block has extra information associated with it, like if it can go BOOM, along
with the position and things like that. If I were to do this using a GUI, probably
color info as well).

This is a pretty popular way of doing it in common physics engines: for example,
see both Box2D and Chipmunk which have different notions of Body and Shape.


Interesting Tidbits
===================

* Drawing the projection of where the block would fall was pretty fun to implement
