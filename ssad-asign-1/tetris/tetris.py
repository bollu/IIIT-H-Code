#!/usr/bin/env python3
# All coordinates are with respect to top left as origin,
# +ve x axis is towards right, +ve y axis is towards bottom.

import curses
import random
import time
import pudb


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

    def __str__(self):
        return "<%s, %s>" % (self.x, self.y)

    @staticmethod
    def zero():
        return Vec(0, 0)

    def in_aabb(self, topleft, dim):
        """Check if is within AABB"""
        # topleft + delta = self
        # delta = self - topleft
        pos_wrt_origin = self - topleft
        return abs(pos_wrt_origin.x) <= abs(dim.x) and \
                abs(pos_wrt_origin.y) <= abs(dim.y)

def clamp(low, cur, high):
    assert (low <= high)

    if cur < low:
        return low
    elif cur > high:
        return high

    return cur


class Shape:
    def __init__(self, shape_arr):
        """
        Parameters
        ==========

        shape_arr: [[Bool]]
        outer dimensions contains x, inner dimension contains y values
        """
        assert isinstance(shape_arr, list)
        assert len(shape_arr) > 0

        row_len = len(shape_arr[0])
        for row in shape_arr:
            assert isinstance(row, list)
            assert len(row) == row_len
            for elem in row:
                assert isinstance(elem, bool)

        xdim = len(shape_arr)
        ydim = len(shape_arr[0])
        self._dim = Vec2(xdim, ydim)
        self._shape = shape_arr
    @property
    def shape(self):
        return self._shape

    @property
    def dim(self):
        return self._dim

    def point_occupied(self, point):
        if point.x < 0 or point.x >= self.dim.x or \
                point.y < 0 or point.y >= self.dim.y:
                    return False

        return self.shape[point.x][point.y]

    @staticmethod
    def shape_from_str(shape_str):
        row_dims = []
        for row in shape_str:
            assert isinstance(row, str)
            row_dims.append(len(row))

        assert(row_dims != [] and len(set(row_dims)) == 1)
        ncols = row_dims[0]
        nrows = len(shape_str)

        shape_arr = [[shape_str[y][x] == 'x' for y in range(nrows)] for x in range(ncols)]
        write_debug_log("%s" % shape_arr)
        return Shape(shape_arr)

    @staticmethod
    def rotate_ccw(shape):
        assert (isinstance(shape, Shape))
        """returns a new shape that is the the given shape
        rotated clockwise"""

        new_shape = [[False for _ in range(shape.dim.x)] for _ in range(shape.dim.y)]

        for x in range(shape.dim.x):
            for y in range(shape.dim.y):
                new_shape[y][shape.dim.x - 1 - x] = shape.shape[x][y]

        return Shape(new_shape)

    @staticmethod
    def rotate_cw(shape):
        assert (isinstance(shape, Shape))
        """returns a new shape that is the the given shape
        rotated clockwise"""

        new_shape = [[False for _ in range(shape.dim.x)] for _ in range(shape.dim.y)]

        for x in range(shape.dim.x):
            for y in range(shape.dim.y):
                new_shape[shape.dim.y - 1 - y][x] = shape.shape[x][y]

        return Shape(new_shape)


class Board:
    def __init__(self, width, height):
        self._dim = Vec2(width, height)
        write_debug_log(str((width, height)))

        self._occupied = [[False for _ in range(height)] for _ in range(width)]

    def point_occupied(self, pos):
        # assert pos.x >= 0 and pos.x <= self.dim.x
        # assert pos.y >= 0 and pos.y < self.dim.y
        if pos.x < 0 or pos.x >= self._dim.x or \
                pos.y < 0 or pos.y >= self._dim.y:
                    return True
        return self._occupied[pos.x][pos.y]

    def freeze_point(self, pos):
        assert(pos.x >= 0 and pos.x < self._dim.x and pos.y >= 0 and
                pos.y < self._dim.y)
        # assert(self._field[pos.x][pos.y] is False)
        self._occupied[pos.x][pos.y] = True

    def unfreeze_point(self, pos):
        assert(pos.x >= 0 and pos.x < self._dim.x and pos.y >= 0 and
                pos.y < self._dim.y)
        # assert(self._field[pos.x][pos.y] is False)
        self._occupied[pos.x][pos.y] = False

    def can_place_shape(self, shape, pos):
        extrema = pos + shape.dim
        if extrema.x > self.dim.x or extrema.y > self.dim.y or \
                pos.x < 0 or pos.y < 0:
                    return False

        for y in range(shape.dim.y):
            for x in range(shape.dim.x):
                delta = Vec2(x, y)
                if shape.point_occupied(delta) and self.point_occupied(pos + delta):
                    return False

        return True

    def _is_row_full(self, y):
        assert y >= 0 and y < self._dim.y
        row_full = True
        for x in range(0, self._dim.x):
            if self._occupied[x][y] is False:
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

            for y in range(bottom_y, 0, -1):
                for x in range(self._dim.x):
                    self._occupied[x][y] = self._occupied[x][y - 1]

            for x in range(self.dim.x):
                self._occupied[x][0] = False

            write_debug_log("clearing full rows")
        for y in range(self._dim.y - 1, 0, -1):
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

    @property
    def dim(self):
        return self._dim

    @property
    def field(self):
        return self._occupied


class Block:
    """Basic Block class that represents all kinds of blocks"""

    def __init__(self, pos, shape):
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
        assert isinstance(shape, Shape)
        self._pos = pos
        self._shape = shape

    @property
    def pos(self):
        return self._pos

    @property
    def dim(self):
        return self.shape.dim

    @property
    def shape(self):
        return self._shape

    def point_occupied(self, point):
        return self._shape.point_occupied(point)

    def set_pos(self, new_pos):
        self._pos = new_pos

    def freeze(self, board):
        """
        To be overridden by derived classes
        """
        for y in range(self.dim.y):
            for x in range(self.dim.x):
                delta = Vec2(x, y)
                if self.point_occupied(delta):
                    board.freeze_point(self.pos + delta)
    def rotate_cw(self):
        """
        Rotates the piece clockwise and returns the new shape
        Return None if this is to be disallowed
        """
        new_shape = Shape.rotate_cw(self.shape)
        return Block(self.pos, new_shape)
    
    def rotate_ccw(self):
        """
        Rotates the piece counter-clockwise and returns the new Block
        Return None if this is to be disallowed
        """
        new_shape = Shape.rotate_ccw(self.shape)
        return Block(self.pos, new_shape)


class VerticalKillBlock(Block):
    def __init__(self, pos, shape):
        Block.__init__(self, pos, shape)

    def freeze(self, board):
        for y in range(0, board.dim.y):
            board.unfreeze_point(Vec2(self.pos.x, y))


def g_make_new_block_shape(pos, board):
    possible_shapes = []
    # Simple Blocks
    LONG = Shape.shape_from_str(["x", "x", "x", "x"])
    T = Shape.shape_from_str(["xxx", " x ", " x "])
    SQUARE = Shape.shape_from_str(["xx", "xx"])
    ZIGZAG = Shape.shape_from_str(["x  ", "xxx", "  x"])

    simple_block_shapes = [SQUARE, T, LONG, ZIGZAG]

    for shape in simple_block_shapes:
        for x in range(0, board.dim.x - shape.dim.x + 1):
            pos = Vec2(x, 0)
            if board.can_place_shape(shape, pos):
                possible_shapes.append(Block(pos, shape))

            cw_shape = Shape.rotate_cw(shape)
            if board.can_place_shape(cw_shape,  pos):
                possible_shapes.append(cw_shape)

            ccw_shape = Shape.rotate_ccw(shape)
            if board.can_place_shape(ccw_shape,  pos):
                possible_shapes.append(cw_shape)

    if len(possible_shapes) == 0:
        return None
    else:
        return possible_shapes[random.randint(0, len(possible_shapes) - 1)]


class Player:
    def __init__(self):
        self._score = 0

    def add_score(self, score_delta):
        self._score += score_delta

    @property
    def score(self):
        return self._score
    
class Game:
    def __init__(self, width, height):

        self.dim = Vec2(width, height)
        self.board = Board(width, height)
        self.block = None
        self._game_over = False
        self._player = Player()

    def update(self, event):
        if self._game_over:
            return

        if self.block is None and self._should_spawn_block():
            write_debug_log("spawning block")
            rand_x = random.randint(0, self.dim.x - 1)
            new_block = g_make_new_block_shape(Vec2(rand_x, 0), self.board)

            if new_block is None:
                write_debug_log("Game Over")
                self._game_over = True
            else:
                self.block = new_block
        else:
            write_debug_log("updating block")
            GRAVITY = Vec2(0, 1)
            block_delta = Vec2(0, 0)

            # Movement Events ----
            if event == EVENT_MOVE_LEFT or event ==  EVENT_MOVE_RIGHT:
                move_delta = Vec2(0, 0)
                if event == EVENT_MOVE_LEFT:
                    block_delta.x = -1
                elif event == EVENT_MOVE_RIGHT:
                    block_delta.x = +1

                # disallow wrong placements
                if not self.board.can_place_shape(self.block.shape, self.block.pos + block_delta + GRAVITY):
                    block_delta = Vec2(0, 0)

            # Fall events
            elif event == EVENT_FALL:
                fall_delta = Vec2(0, 0)
                while self.board.can_place_shape(self.block.shape, self.block.pos + GRAVITY + fall_delta): 
                        fall_delta.y += 1
                block_delta += fall_delta
                self.block.set_pos(self.block.pos + fall_delta)

            # Rotation Events --
            elif event == EVENT_ROTATE_CW or event == EVENT_ROTATE_CCW:
                if event == EVENT_ROTATE_CW:
                    new_block = self.block.rotate_cw()
                else:
                    new_block = self.block.rotate_ccw()
                    
                if self.board.can_place_shape(new_block.shape, new_block.pos):
                    self.block = new_block
                else:
                    write_debug_log("cannot place shape like that")

            # Update physics
            new_pos = self.block.pos + block_delta + GRAVITY
            if not self.board.can_place_shape(self.block.shape, new_pos):
                write_debug_log("Block Frozen")
                # self.block.pos.y += 1
                self.block.freeze(self.board)
                self.block = None
                num_rows_cleared = self.board.clear_full_rows()
                self.player.add_score(num_rows_cleared * 100)
            else:
                write_debug_log("Block Moving. Vel: %s" % (block_delta + GRAVITY))
                self.block.set_pos(new_pos)
                write_debug_log("Block position: %s" % self.block.pos)

    @property
    def player(self):
        return self._player

    def is_game_over(self):
        return self._game_over

    def _should_spawn_block(self):
        return True

# Oh how I miss sum types...
EVENT_NONE = "EVENT_NONE"
EVENT_MOVE_LEFT = "EVENT_MOVE_LEFT"
EVENT_FALL = "EVENT_FALL"
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


    def _draw_debug_log(self):
        self.win.addstr(0, 0, self.last_event,
                curses.A_REVERSE)

        self.win.addstr(1, 0, get_debug_string(),
                curses.A_REVERSE)

    def _draw_score(self, game):
        self.win.addstr(0, 0, "Score: %d" % (game.player.score, ))

    def _draw_borders(self, max_width, max_height):

        for y in range(max_height):
            self.addch(Vec2(0, y), '|')
            self.addch(Vec2(width + 1, y), '|')

        for x in range(max_width+2):
            self.addch(Vec2(x, max_height), '-')

        extreme_points = [Vec2(0, max_height), Vec2(max_width+1, max_height)]
        for point in extreme_points:
            self.addch(point, '+')
    def draw(self, game):
        self.win.clear()
        self._draw_score(game)


        self._draw_borders(self.MAX_WIDTH, self.MAX_HEIGHT)

        for y in range(self.MAX_HEIGHT):
            for x in range(self.MAX_WIDTH):
                curr_pos = Vec2(x, y)
                if game.board.field[x][y]:
                    self.addch(CLIView.model_to_view(curr_pos), '@')

        if game.block is not None:
            for y in range(game.block.dim.y):
                for x in range(game.block.dim.x):
                    if game.block.point_occupied(Vec2(x, y)):
                        curr_pos = game.block.pos + Vec2(x, y)
                        self.addch(CLIView.model_to_view(curr_pos), 'x')

        self.win.refresh()

    def gameover(self, game):
        self.win.clear()
        self.win.addstr("Game over! Well played!")
        self.win.addstr("You scored: " + str(game.player.score))
        self.win.refresh()

    def quit(self):
        curses.nocbreak()
        self.stdscr.keypad(0)
        curses.echo()

    def get_event(self):
        event = EVENT_NONE

        # keep taking events till we get the last one
        key = None
        try:
            while True:
                key = self.win.getkey()
        except Exception:
            pass

        if key == 'q':
            event = EVENT_QUIT
        if key == 'j':
            event = EVENT_ROTATE_CW
        elif key == 'k':
            event = EVENT_ROTATE_CCW
        elif key == 'a':
            event = EVENT_MOVE_LEFT
        elif key == 'd':
            event = EVENT_MOVE_RIGHT
        elif key == 's':
            event = EVENT_FALL

        self.last_event = event
        return event

RENDER_STEP_TIME = 1.0 / 60.0
NUM_FRAMES_TO_UPDATE = 3

if __name__ == "__main__":
    width, height = (1, 20)
    view = CLIView(width, height)
    game = Game(width, height)

    prev_time = time.time()
    render_time_accum = 0
    nonupdated_frames_accum = 0

    quit = False

    while not quit:
        current_time = time.time()
        render_time_accum += current_time - prev_time

        while render_time_accum > RENDER_STEP_TIME:
            render_time_accum -= RENDER_STEP_TIME
            view.draw(game)
            nonupdated_frames_accum += 1
            if nonupdated_frames_accum > NUM_FRAMES_TO_UPDATE:
                nonupdated_frames_accum -= NUM_FRAMES_TO_UPDATE
                curses.noqiflush()
                event = view.get_event()
                if event == EVENT_QUIT:
                    view.quit()
                    quit = True
                else:
                    game.update(event)

            if game.is_game_over():
                quit = True
                view.gameover(game)

        prev_time = time.time()
    # reset stuff



