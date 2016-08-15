#!/usr/bin/env python3
# All coordinates are with respect to top left as origin,
# +ve x axis is towards right, +ve y axis is towards bottom.

import curses
import random
import time


DEBUG_LOG = []
def write_debug_log(string):
    global DEBUG_LOG
    DEBUG_LOG.append(string)
    # take only last 5 records
    DEBUG_LOG = DEBUG_LOG[-5:]

def get_debug_string():
    global DEBUG_LOG
    return "\n".join(DEBUG_LOG)

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
        self.dim = Vec2(width, height)
        write_debug_log(str((width, height)))
        
        self.field = [[False for _ in range(height)] for _ in range(width)]
        

    def point_occupied(self, pos):
        assert pos.x >= 0 and pos.x <= self.dim.x
        assert pos.y >= 0 and pos.y < self.dim.y
        return self.field[pos.x][pos.y]

    def _is_row_full(self, y):
        assert y >= 0 and y < self.dim.y
        row_full = True
        for x in range(0, self.dim.x):
            if self.field[x][y] == False:
                row_full = False
                break

        return row_full
    
    def _clear_first_full_row(self):
        """
        Clears the first possible full row. Return
        whether a row was cleared or not
        """
        def _shift_rows_down(bottom_y):
            assert bottom_y > 0 and bottom_y <= self.dim.y - 1

            y = bottom_y
            for y in range(bottom_y, 0, -1):
                for x in range(self.dim.x):
                    self.field[x][y] = self.field[x][y - 1]
    
            for x in range(self.dim.x):
                self.field[x][0] = False

        for y in range(self.dim.y - 1, 0, -1):
            if self._is_row_full(y):
                write_debug_log("row %s is FULL" % y)
                _shift_rows_down(y)
                return True

        return False

    def clear_full_rows(self):
        """
        Tries to clear rows that are fully formed
        returns number of cleared rows
        """

        num_rows_cleared = 0

        still_clearing = True
        while still_clearing:
            # try to clear the first row possible
            # if not cleared, then we are done
            # if we did clear, then there maybe more
            still_clearing = self._clear_first_full_row()
            num_rows_cleared += 1
        return num_rows_cleared

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

    def point_occupied(self, point):
        """Return whether the point is contained in the Block"""
        raise NotImplementedError()

    def does_collide_board(self, board):
        """Return whether there is collision with the Board"""
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
        ncols = row_dims[0]
        nrows = len(shape)

        # for r in shape:
        #    for c in r:
        #        assert (c == 'x' or c == ' ')

        # convert from a shape[row][col] representation to a 
        # shape[x][y] repressentation
        self.shape = [[shape[y][x] == 'x'
                        for y in range(nrows)]
                        for x in range(ncols)]

        width = len(shape)
        height = row_dims[0]
    
        Block.__init__(self, pos, Vec2(height, width))


    def point_occupied(self, point):
        point_wrt_pos = point - self.pos
        
        
        if not ((point_wrt_pos.x >= 0 and point_wrt_pos.x < self.dim.x)
                and (point_wrt_pos.y >= 0 and point_wrt_pos.y < self.dim.y)):
            return False

        return self.shape[point_wrt_pos.x][point_wrt_pos.y]


    @property
    def extrema(self):
        return self.pos + self.dim

    def does_collide_board(self, board):
        for x in range(self.dim.x):
            for y in range(self.dim.y):
                delta = Vec2(x, y)
                if board.point_occupied(self.pos + delta):
                    return True


        return False
    
    def should_freeze(self, board):
        """returns if the block should be frozen on the board due to
           collisions with extreme pieces"""
        if self.pos.y + self.dim.y >= board.dim.y:
            return True


        for y in range(self.dim.y):
            for x in range(self.dim.x):
                if board.point_occupied(self.pos + Vec2(x, y + 1)):
                    return True

        return False

    def freeze(self, board):
        for y in range(self.dim.y):
            for x in range(self.dim.x):
                if self.shape[x][y]:
                    board.field[self.pos.x + x][self.pos.y + y] = True


def g_spawn_block(pos, board):
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
    while True:
        block =  SimpleBlock(pos, block_shapes[random.randint(0, len(block_shapes) - 1)])
         
        if block.pos.x >= 0 and block.extrema.x <= board.dim.x and \
           block.pos.y >= 0 and block.extrema.y <= board.dim.y and \
           not block.does_collide_board(board):
                return block

class Game:
    def __init__(self, width, height):

        self.dim = Vec2(width, height)
        self.board = Board(width, height)
        self.block = None

    def update(self, event):
        if self.block == None and self.should_spawn_block():
            rand_x = random.randint(0, self.dim.x - 1)
            self.block = g_spawn_block(Vec2(rand_x, 0), self.board)
        elif self.block.should_freeze(self.board):
             self.block.freeze(self.board)
             self.block = None
             self.board.clear_full_rows()
        else:
            block_extrema = self.block.pos + self.block.dim
            if event == EVENT_MOVE_LEFT and self.block.pos.x > 0:
                self.block.pos.x -= 1
            elif event == EVENT_MOVE_RIGHT and block_extrema.x < self.board.dim.x:
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
        
        self.RENDER_ORIGIN = Vec2(10, 10)
        # +1, +1 for the borders
        self.win = curses.newwin(self.RENDER_ORIGIN.y + self.MAX_HEIGHT + 200,
                                 self.RENDER_ORIGIN.x + self.MAX_WIDTH + 200, 0, 0,)
        self.win.nodelay(1)
        self.last_event = ""

    @staticmethod
    def model_to_view(pos):
        return Vec2(pos.x + 1, pos.y)

    def addch(self, view_pos, char):
        render_pos = view_pos + self.RENDER_ORIGIN
        self.win.addch(render_pos.y, render_pos.x, char)

    def draw(self, game):
        self.win.clear()
        self.win.addstr(0, 0, self.last_event,
              curses.A_REVERSE)

        self.win.addstr(1, 0, get_debug_string(),
              curses.A_REVERSE)

        def draw_borders(max_width, max_height):

            for y in range(max_height):
                self.addch(Vec2(0, y), '|')
                self.addch(Vec2(width + 1, y), '|')

            for x in range(max_width+2):
                self.addch(Vec2(x, max_height), '-')
            

            extreme_points = [Vec2(0, max_height), Vec2(max_width+1, max_height)]

            for point in extreme_points:
                self.addch(point, '+')

        draw_borders(self.MAX_WIDTH, self.MAX_HEIGHT)

        for y in range (self.MAX_HEIGHT):
            for x in range(self.MAX_WIDTH):
                curr_pos = Vec2(x, y)

                if game.block is not None:
                    if game.block.point_occupied(curr_pos):
                        self.addch(CLIView.model_to_view(curr_pos), '#')
                
                if game.board.field[x][y]:
                    self.addch(CLIView.model_to_view(curr_pos), '@')

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

TIME_STEP_TIME = 1.0 / 30.0

if __name__ == "__main__":
    width, height = (5, 10)
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



