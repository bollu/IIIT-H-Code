#!/usr/bin/env python3
# All coordinates are with respect to top left as origin,
# +ve x axis is towards right, +ve y axis is towards bottom.

import curses
import random
import time


class Vec2:
    def __init__(self, x, y):
        self.x = x
        self.y = y
    
    def __sub__(self, other):
        assert isinstance(other, Vec2)
        return Vec2(self.x - other.x, self.y - other.y)
    
    def __add__(self, other):
        assert isinstance(other, Vec2)
        return Vec2(self.x + other.x, self.y + other.y)


    @classmethod
    def zero():
        return Vec(0, 0)
    
    def in_aabb(self, topleft, dim):
        """Check if is within AABB"""
        # topleft + delta = self
        # delta = self - topleft
        pos_wrt_origin = self - topleft
        return abs(pos_wrt_origin.x) <= abs(dim.x) and \
               abs(pos_wrt_origin.y) <= abs(dim.y)

class Board:
    def __init__(self, width, height):
        self.width = width
        self.height = height

class Block:
    """Basic Block class that represents all kinds of blocks"""

    def __init__(self, pos, dim):
        """
        Create the block.
        In local coordinates, origin is top left.
        (0, 0)
        +--> +x axis
        |
        v
        +y axis

        Parameters:
        ----------
        position: Vec2
            position with respect to game coordinates
        dim: Vec2
            dimensions of the block with respect to origin
        """
        assert isinstance(pos, Vec2)
        assert isinstance(dim, Vec2)
        self.pos = pos
        self.dim = dim

    def contains(self, point):
        """Return whether the point is contained in the Block"""
        raise NotImplementedError()

    def rotate(self):
        pass

    def moveLeft(self):
        pass

    def moveRight(self):
        pass

    def draw(self):
        pass

class SimpleBlock(Block):
    def __init__(self, pos, shape):
        """
        Initialize a block
        """
        assert(isinstance(shape, list))

        row_dims = []
        for row in shape:
            assert isinstance(row, str)
            row_dims.append(len(row))

        assert(row_dims != [] and len(set(row_dims)) == 1)

        # for r in shape:
        #    for c in r:
        #        assert (c == 'x' or c == ' ')

        #outer dimension y, inner dimension x
        self.shape = shape

        width = len(shape)
        height = row_dims[0]
    
        Block.__init__(self, pos, Vec2(height, width))


    def contains(self, point):
        point_wrt_pos = point - self.pos
        
        
        if not ((point_wrt_pos.x >= 0 and point_wrt_pos.x < self.dim.x)
                and (point_wrt_pos.y >= 0 and point_wrt_pos.y < self.dim.y)):
            return False

        return self.shape[point_wrt_pos.y][point_wrt_pos.x] == 'x'

    def should_freeze(self, board):
        """returns if the block should be frozen on the board"""
        pass


def g_spawn_block(pos):
    SQUARE = ["xx",
              "xx"]
    LONG = ["x",
            "x",
            "x",
            "x"]

    T = ["xxx",
         " x ",
         " x "]

    block_shapes = [SQUARE, LONG, T]
    return SimpleBlock(pos, block_shapes[random.randint(0, len(block_shapes) - 1)])

class Game:
    def __init__(self, width, height):

        self.dim = Vec2(width, height)
        self.board = Board(width, height)
        self.block = None

    def update(self, event):
        if self.block == None and self.should_spawn_block():
            rand_x = random.randint(0, self.dim.x - 1)
            self.block = g_spawn_block(Vec2(rand_x, 0))
        elif self.block.should_freeze(self.board):
            self.block.freeze(self.board)
        else:
            if event == EVENT_MOVE_LEFT:
                self.block.pos.x -= 1
            elif event == EVENT_MOVE_RIGHT:
                self.block.pos.x += 1

            self.tick_block()

    def tick_block(self):
        self.block.pos.y += 1


    def should_spawn_block(self):
        return True



# Oh how I pine for sum types...
EVENT_NONE = "EVENT_NONE"
EVENT_MOVE_LEFT = "EVENT_MOVE_LEFT"
EVENT_MOVE_RIGHT = "EVENT_MOVE_RIGHT"
EVENT_ROTATE_CW = "EVENT_ROTATE_CW"
EVENT_ROTATE_CCW = "EVENT_ROTATE_CCW"
EVENT_QUIT = "EVENT_QUIT"

class View:
    def handle_events():
        pass
    def draw_game(game):
        pass


class CLIView(View):
    def __init__(self, max_width, max_height):
        self.stdscr = curses.initscr()
        curses.noecho()
        curses.cbreak()
        self.stdscr.keypad(1)

        self.MAX_WIDTH = max_width
        self.MAX_HEIGHT = max_height
        
        self.win = curses.newwin(self.MAX_HEIGHT, self.MAX_WIDTH, 0, 0,)
        self.win.nodelay(1)
        self.last_event = ""


    def draw(self, game):
        self.win.clear()
        self.win.addstr(0, 0, self.last_event,
              curses.A_REVERSE)

        for y in range (self.MAX_HEIGHT):
            for x in range(self.MAX_WIDTH):
                curr_pos = Vec2(x, y)

                if game.block is not None:
                    if game.block.contains(curr_pos):
                        self.win.addch(y, x, '#')

        self.win.refresh()
    def quit(self):
        curses.nocbreak()
        self.stdscr.keypad(0)
        curses.echo()

    def get_event(self):
        event = EVENT_NONE
        try:
            key = self.win.getkey()
            if key == 'w':
                event = EVENT_ROTATE_CW
            elif key == 's':
                event = EVENT_ROTATE_CCW
            elif key == 'a':
                event = EVENT_MOVE_LEFT
            elif key == 'd':
                event = EVENT_MOVE_RIGHT
            elif key == 'q':
                event = EVENT_QUIT
        except Exception:
            self.last_event = "EXCEPTION"
            pass

        self.last_event = event
        return event

TIME_STEP_TIME = 1.0 / 15.0

if __name__ == "__main__":
    width, height = (50, 50)
    view = CLIView(width, height)
    game = Game(width, height)

    prev_time = time.time()
    time_accum = 0

    quit = False

    while not quit:
        current_time = time.time()
        time_accum += current_time - prev_time

        while time_accum > TIME_STEP_TIME:
            time_accum -= TIME_STEP_TIME

            event = view.get_event()
            #dostuff part of code
            if event == EVENT_QUIT:
                view.quit()
                quit = True
            else:
                game.update(event)
                view.draw(game)
    
        prev_time = time.time()
    # reset stuff



