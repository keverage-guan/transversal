# File: transversal_examples.py
# Description: Figures and worked examples for the transversal tic-tac-toe
# write-up. Running this module regenerates every image and CSV in
# ``examples/``.

"""Figures and worked examples for the transversal tic-tac-toe write-up.

Running this module regenerates every image and CSV in ``examples/``.
"""

from __future__ import annotations

import csv
import os
import random
from itertools import permutations

import matplotlib

matplotlib.use("Agg")

import matplotlib.patches as mpatches
import matplotlib.pyplot as plt


# Configuration

OUTDIR = "examples"

DRAW_ATTEMPTS = 200_000
SEED = 42

X_COLOR = "#2b6cb0"
O_COLOR = "#c53030"
GRID_COLOR = "#333333"
AXB_COLOR = "#ede6d6"

# Light gray used for structural regions such as H and A x B.
LIGHT_GRAY = "#d9d9d9"

# Stroke and fill colour for each player's stones.
PLAYER_STYLE = {
    "X": (X_COLOR, "#dbeafe"),
    "O": (O_COLOR, "#fde8e8"),
}


# Basic game utilities

def cells_for_player(moves, player):
    """Return the set of cells owned by player."""
    return {(r, c) for who, r, c in moves if who == player}


def winning_transversal(moves, player, n):
    """
    Return the cells of a transversal owned by player.

    A transversal contains exactly one cell from every row and every
    column.  Returns a list of (row, column) cells, or None if player
    does not currently have a transversal.
    """
    cells = cells_for_player(moves, player)

    # Check every possible row-to-column assignment for one that is
    # fully covered by the player's cells.
    for cols in permutations(range(1, n + 1)):
        transversal = [(r, cols[r - 1]) for r in range(1, n + 1)]

        if all(cell in cells for cell in transversal):
            return transversal

    return None


def has_transversal(moves, player, n):
    """Return True iff player owns a transversal."""
    return winning_transversal(moves, player, n) is not None


def outcome(moves, n):
    """
    Return the current game outcome.

    Returns:
        "X"       if X has won
        "O"       if O has won
        "draw"    if the board is full without a winner
        "ongoing" otherwise
    """
    x_wins = has_transversal(moves, "X", n)
    o_wins = has_transversal(moves, "O", n)

    if x_wins and o_wins:
        raise ValueError("Invalid position: both players have transversals.")

    if x_wins:
        return "X"

    if o_wins:
        return "O"

    if len(moves) == n * n:
        return "draw"

    return "ongoing"


def occupied_cells(moves):
    """Return the set of cells holding a stone of either colour."""
    return {(r, c) for _, r, c in moves}


def legal_moves(moves, n):
    """Return all currently unoccupied cells."""
    occupied = occupied_cells(moves)

    return [
        (r, c)
        for r in range(1, n + 1)
        for c in range(1, n + 1)
        if (r, c) not in occupied
    ]


def add_move(moves, player, cell):
    """Return a new history with one move appended."""
    row, column = cell
    return moves + [(player, row, column)]


def interleave(x_cells, o_cells):
    """
    Interleave two lists of cells into an alternating history.

    X moves first.  The shorter list simply runs out, which lets a
    winning line for either player be described by its own cells alone.
    """
    moves = []

    for i in range(max(len(x_cells), len(o_cells))):
        if i < len(x_cells):
            moves.append(("X", *x_cells[i]))

        if i < len(o_cells):
            moves.append(("O", *o_cells[i]))

    return moves


# Validation

def validate_history(moves, n, expected_outcome=None):
    """
    Validate an entire game history.

    Checks:
      - moves alternate X/O;
      - all cells are legal;
      - nobody wins before the final move;
      - the final outcome is as expected.
    """
    if len(moves) > n * n:
        raise ValueError("History contains more than n^2 moves.")

    occupied = set()

    for ply, (player, r, c) in enumerate(moves, start=1):
        expected_player = "X" if ply % 2 == 1 else "O"

        if player != expected_player:
            raise ValueError(
                f"Ply {ply}: expected {expected_player}, got {player}."
            )

        if not (1 <= r <= n and 1 <= c <= n):
            raise ValueError(f"Ply {ply}: ({r}, {c}) is outside the board.")

        if (r, c) in occupied:
            raise ValueError(f"Ply {ply}: ({r}, {c}) was already occupied.")

        occupied.add((r, c))

        # Re-check the outcome after every intermediate ply to make sure
        # the game did not already end before the history claims it did.
        if ply < len(moves) and outcome(moves[:ply], n) != "ongoing":
            raise ValueError(f"Game ended at ply {ply}, but history continues.")

    final_outcome = outcome(moves, n)

    if expected_outcome is not None and final_outcome != expected_outcome:
        raise ValueError(
            f"Expected outcome {expected_outcome}, got {final_outcome}."
        )

    return final_outcome


# Constructing decisive games

def make_x_win(n):
    """Construct an X win using a non-diagonal transversal."""
    if n != 5:
        raise ValueError("This concrete X-win construction is designed for n=5.")

    moves = interleave(
        x_cells=[(1, 3), (2, 5), (3, 1), (4, 4), (5, 2)],
        o_cells=[(1, 1), (4, 2), (2, 3), (5, 5)],
    )

    validate_history(moves, n, expected_outcome="X")

    return moves


def make_o_win(n):
    """Construct an O win using a non-diagonal transversal."""
    if n != 5:
        raise ValueError("This concrete O-win construction is designed for n=5.")

    moves = interleave(
        x_cells=[(1, 1), (3, 2), (5, 4), (2, 3), (4, 1)],
        o_cells=[(1, 4), (2, 1), (3, 5), (4, 2), (5, 3)],
    )

    validate_history(moves, n, expected_outcome="O")

    return moves


# Constructing a draw

def random_draw_attempt(n, rng):
    """Try to construct a draw by randomly filling the board."""
    moves = []

    for ply in range(n * n):
        player = "X" if ply % 2 == 0 else "O"

        # Only consider moves that do not immediately hand the mover a
        # transversal, since the goal here is a full board with no winner.
        safe = [
            cell
            for cell in legal_moves(moves, n)
            if not has_transversal(add_move(moves, player, cell), player, n)
        ]

        if not safe:
            return None

        moves = add_move(moves, player, rng.choice(safe))

    return moves if outcome(moves, n) == "draw" else None


def make_draw(n, attempts=DRAW_ATTEMPTS, seed=SEED):
    """Search randomly for a complete draw."""
    rng = random.Random(seed)

    for attempt in range(1, attempts + 1):
        moves = random_draw_attempt(n, rng)

        if moves is not None:
            print(f"Found {n}x{n} draw after {attempt:,} attempts.")
            validate_history(moves, n, expected_outcome="draw")
            return moves

        if attempt % 10_000 == 0:
            print(f"  tried {attempt:,} draw constructions...")

    raise RuntimeError(
        f"Could not find a draw after {attempts:,} attempts. "
        f"Try increasing DRAW_ATTEMPTS."
    )


# Saving histories

def save_history_csv(moves, path):
    """Save a game history to CSV."""
    with open(path, "w", newline="") as fh:
        writer = csv.writer(fh)

        writer.writerow(["ply", "player", "move_number", "row", "column"])

        move_numbers = {"X": 0, "O": 0}

        for ply, (player, row, column) in enumerate(moves, start=1):
            move_numbers[player] += 1

            writer.writerow([ply, player, move_numbers[player], row, column])


# Drawing primitives
#
# Every figure in this module draws the same handful of things: a grid,
# filled cells, stones, boxed cells and bullseye markers.  Cells are
# addressed by (row, column) with 1-based indices; the matching patch
# origin is (column - 1, row - 1), with the y axis running downwards.

def setup_board_axes(ax, n, xlim=None, ylim=None):
    """Configure an axis to hold an n x n board with row 1 on top."""
    ax.set_xlim(*(xlim if xlim is not None else (0, n)))
    # The y-limits are inverted so that row 1 is drawn at the top of the
    # figure, matching how the board is described elsewhere.
    ax.set_ylim(*(ylim if ylim is not None else (n, 0)))
    ax.set_aspect("equal")


def draw_grid(ax, n, color=GRID_COLOR, linewidth=0.95, zorder=1):
    """Draw the n x n grid lines."""
    for i in range(n + 1):
        ax.plot([0, n], [i, i], color=color, lw=linewidth, zorder=zorder)
        ax.plot([i, i], [0, n], color=color, lw=linewidth, zorder=zorder)


def fill_cell(
    ax,
    row,
    column,
    facecolor,
    edgecolor="none",
    linewidth=0,
    linestyle="-",
    zorder=0,
):
    """Fill a single cell with a solid colour."""
    ax.add_patch(
        mpatches.Rectangle(
            (column - 1, row - 1),
            1,
            1,
            facecolor=facecolor,
            edgecolor=edgecolor,
            linewidth=linewidth,
            linestyle=linestyle,
            zorder=zorder,
        )
    )


def fill_region(
    ax,
    rows,
    columns,
    facecolor,
    edgecolor="none",
    linewidth=0,
    linestyle="-",
    zorder=0,
):
    """Fill the rectangle spanned by contiguous rows and columns."""
    row_start, row_end = min(rows), max(rows)
    col_start, col_end = min(columns), max(columns)

    ax.add_patch(
        mpatches.Rectangle(
            (col_start - 1, row_start - 1),
            col_end - col_start + 1,
            row_end - row_start + 1,
            facecolor=facecolor,
            edgecolor=edgecolor,
            linewidth=linewidth,
            linestyle=linestyle,
            zorder=zorder,
        )
    )


def draw_stone(ax, row, column, player, label, fontsize, linewidth=1.1, zorder=2):
    """Draw one stone: a tinted cell plus its label."""
    color, face = PLAYER_STYLE[player]

    fill_cell(
        ax,
        row,
        column,
        facecolor=face,
        edgecolor=GRID_COLOR,
        linewidth=linewidth,
        zorder=zorder,
    )

    ax.text(
        column - 0.5,
        row - 0.5,
        label,
        ha="center",
        va="center",
        fontsize=fontsize,
        color=color,
        fontweight="bold",
        zorder=zorder + 1,
    )


def draw_numbered_stones(ax, cells, player, fontsize, linewidth=1.1, zorder=2):
    """Draw a list of cells as stones labelled X_1, X_2, ... for one player."""
    for move_number, (row, column) in enumerate(cells, start=1):
        draw_stone(
            ax,
            row,
            column,
            player,
            rf"${player}_{{{move_number}}}$",
            fontsize,
            linewidth=linewidth,
            zorder=zorder,
        )


def draw_history_stones(ax, moves, fontsize, linewidth=1.2, zorder=2):
    """Draw a full move history, numbering each player's stones separately."""
    move_numbers = {"X": 0, "O": 0}

    for player, row, column in moves:
        move_numbers[player] += 1

        draw_stone(
            ax,
            row,
            column,
            player,
            rf"${player}_{{{move_numbers[player]}}}$",
            fontsize,
            linewidth=linewidth,
            zorder=zorder,
        )


def box_cell(ax, row, column, color="black", linewidth=3, zorder=4):
    """Outline a cell with a heavy border that is never clipped."""
    x0, x1 = column - 1, column
    y0, y1 = row - 1, row

    edges = [
        ([x0, x1], [y0, y0]),
        ([x0, x1], [y1, y1]),
        ([x0, x0], [y0, y1]),
        ([x1, x1], [y0, y1]),
    ]

    for xs, ys in edges:
        ax.plot(
            xs,
            ys,
            color=color,
            linewidth=linewidth,
            solid_capstyle="butt",
            zorder=zorder,
            clip_on=False,
        )


def draw_target(ax, row, column, color="#555555", zorder=6):
    """Draw a bullseye marking a forced but as yet unplayed cell."""
    center = (column - 0.5, row - 0.5)

    rings = [
        (0.36, "none", color, 2.0, zorder),
        (0.17, "none", color, 1.7, zorder),
        (0.055, color, "none", 0, zorder + 1),
    ]

    for radius, facecolor, edgecolor, linewidth, ring_zorder in rings:
        ax.add_patch(
            mpatches.Circle(
                center,
                radius=radius,
                facecolor=facecolor,
                edgecolor=edgecolor,
                linewidth=linewidth,
                zorder=ring_zorder,
            )
        )


def tick_rows(ax, rows, color="#111111", linewidth=2.0, length=0.13, zorder=4):
    """Mark a set of rows with a short stub to the left of the board."""
    for row in rows:
        ax.plot(
            [-length, 0],
            [row - 0.5, row - 0.5],
            color=color,
            linewidth=linewidth,
            solid_capstyle="butt",
            clip_on=False,
            zorder=zorder,
        )


def tick_columns(ax, columns, color="#111111", linewidth=2.0, length=0.13, zorder=4):
    """Mark a set of columns with a short stub above the board."""
    for column in columns:
        ax.plot(
            [column - 0.5, column - 0.5],
            [-length, 0],
            color=color,
            linewidth=linewidth,
            solid_capstyle="butt",
            clip_on=False,
            zorder=zorder,
        )


def label_H(ax, x=4.0, y=5.20, fontsize=14, color="black"):
    """Label the open block H just below the board."""
    ax.text(
        x,
        y,
        r"$H$",
        ha="center",
        va="top",
        fontsize=fontsize,
        color=color,
        fontweight="bold",
        clip_on=False,
    )


def clean_axes(ax):
    """Strip ticks and spines."""
    ax.set_xticks([])
    ax.set_yticks([])

    for spine in ax.spines.values():
        spine.set_visible(False)


def save_figure(fig, path, dpi, pad_inches=None, announce=False):
    """Save with a tight bounding box and close the figure."""
    kwargs = {"dpi": dpi, "bbox_inches": "tight"}

    if pad_inches is not None:
        kwargs["pad_inches"] = pad_inches

    fig.savefig(path, **kwargs)
    plt.close(fig)

    if announce:
        print(f"Wrote {path}")


def out(output_dir, filename):
    """Join a filename onto the output directory."""
    return os.path.join(output_dir, filename)


# Drawing complete game histories

def draw_game_board(
    moves,
    n,
    path,
    boxed_cells=(),
    box_linewidth=3,
    mark_empty_boxes=False,
):
    """
    Draw a position, optionally boxing a set of cells.

    Boxed cells that are still empty are marked with "!" when
    ``mark_empty_boxes`` is set; this is how open threats are shown.
    """
    boxed_cells = set(boxed_cells)
    occupied = occupied_cells(moves)

    fig, ax = plt.subplots(figsize=(1.05 * n + 1, 1.05 * n + 1))

    setup_board_axes(ax, n)
    draw_grid(ax, n, linewidth=1.2)
    draw_history_stones(ax, moves, fontsize=32, linewidth=1.2)

    for row, column in boxed_cells:
        box_cell(ax, row, column, linewidth=box_linewidth)

        # Only stamp the "!" marker for boxed cells that have not been
        # played yet, since occupied cells already show a stone.
        if mark_empty_boxes and (row, column) not in occupied:
            ax.text(
                column - 0.5,
                row - 0.5,
                "!",
                ha="center",
                va="center",
                fontsize=24,
                fontweight="bold",
                color="black",
                zorder=5,
            )

    clean_axes(ax)
    fig.tight_layout()
    save_figure(fig, path, dpi=300)


def draw_board(moves, n, path, highlight_final=True):
    """Draw a game history, boxing the winning transversal if there is one."""
    winning_cells = set()

    if highlight_final and moves:
        result = outcome(moves, n)

        if result in ("X", "O"):
            transversal = winning_transversal(moves, result, n)

            if transversal is not None:
                winning_cells = set(transversal)

    draw_game_board(moves, n, path, boxed_cells=winning_cells, box_linewidth=3)


def draw_phase2_board(moves, n, path, threat_cells=None):
    """Draw an intermediate Phase 2 position, boxing the live threats."""
    draw_game_board(
        moves,
        n,
        path,
        boxed_cells=threat_cells or (),
        box_linewidth=4,
        mark_empty_boxes=True,
    )


# Phase 1 open-block invariant figure

def consecutive_blocks(values):
    """Group sorted values into maximal runs of consecutive integers."""
    if not values:
        return []

    values = sorted(values)

    blocks = []
    start = previous = values[0]

    for value in values[1:]:
        if value == previous + 1:
            previous = value
        else:
            blocks.append((start, previous))
            start = previous = value

    blocks.append((start, previous))

    return blocks


def draw_phase1_invariant_figure(output_dir=OUTDIR):
    """
    Draw three separate illustrations showing maintenance of the
    open-block invariant during Phase 1.
    """
    os.makedirs(output_dir, exist_ok=True)

    n = 5

    panels = [
        (
            "phase1_invariant_a.png",
            [("X", 1, 1)],
            {2, 3, 4, 5},
            {2, 3, 4, 5},
        ),
        (
            "phase1_invariant_b.png",
            [("X", 1, 1), ("O", 3, 4)],
            {2, 3, 4, 5},
            {2, 3, 4, 5},
        ),
        (
            "phase1_invariant_c.png",
            [("X", 1, 1), ("O", 3, 4), ("X", 3, 2)],
            {2, 4, 5},
            {2, 3, 4, 5},
        ),
    ]

    for filename, moves, open_rows, open_cols in panels:
        fig, ax = plt.subplots(figsize=(3.15, 3.15))

        setup_board_axes(ax, n)

        # Shade the still-open rectangular blocks so the invariant is
        # visible as a shaded region rather than just implied by the moves.
        for row_start, row_end in consecutive_blocks(open_rows):
            for col_start, col_end in consecutive_blocks(open_cols):
                fill_region(
                    ax,
                    (row_start, row_end),
                    (col_start, col_end),
                    facecolor="#C5C6C7",
                )

        draw_grid(ax, n, linewidth=1.0)
        draw_history_stones(ax, moves, fontsize=21, linewidth=1.1)

        clean_axes(ax)

        fig.subplots_adjust(left=0.02, right=0.98, top=0.98, bottom=0.02)

        save_figure(
            fig,
            out(output_dir, filename),
            dpi=400,
            pad_inches=0.02,
            announce=True,
        )


# Tie-break and Claims A, A' figure

ADMISSIBLE_COLOR = "#b7e4c7"
ADMISSIBLE_LABEL_COLOR = "#245c38"
L1_COLOR = "#c6dbef"
L2_COLOR = "#f4c6c6"
INTERSECTION_COLOR = "#d0d0d0"


def _annotate_o_stone(ax, row, column, fontsize=22, label_fontsize=10.5, zorder=4):
    """Write O and the subscript (x_{n-2}) inside a cell."""
    ax.text(
        column - 0.5,
        row - 0.5,
        r"$O$",
        ha="center",
        va="center",
        fontsize=fontsize,
        color=O_COLOR,
        fontweight="bold",
        zorder=zorder,
    )

    ax.text(
        column - 0.5,
        row - 0.35,
        r"$(x_{n-2})$",
        ha="center",
        va="top",
        fontsize=label_fontsize,
        color=O_COLOR,
        zorder=zorder,
    )


def _new_claims_axes(figsize=(4.85, 4.28), xlim=(-0.72, 6.35), ylim=(5.48, -0.72)):
    """Create the shared axis layout used by the tie-break/claims panels."""
    fig, ax = plt.subplots(figsize=figsize)

    ax.set_xlim(*xlim)
    ax.set_ylim(*ylim)
    ax.set_aspect("equal")

    return fig, ax


def _draw_tiebreak_panel(path, o_cell, x_cells, admissible, crossed, adjust_right):
    """
    Draw one tie-break panel.

    H is the 2x2 open block in rows {4,5} x columns {4,5} immediately
    before X's (n-1)-st move.  Which of its corners are admissible
    depends on whether O's latest stone lies inside H.
    """
    n = 5

    fig, ax = _new_claims_axes()

    fill_region(
        ax,
        (4, 5),
        (4, 5),
        facecolor=LIGHT_GRAY,
        edgecolor="#555555",
        linewidth=1.8,
    )

    for row, column in admissible:
        fill_cell(ax, row, column, facecolor=ADMISSIBLE_COLOR, zorder=0.5)

    draw_grid(ax, n)
    draw_numbered_stones(ax, x_cells, "X", fontsize=24)

    fill_cell(
        ax,
        *o_cell,
        facecolor=PLAYER_STYLE["O"][1],
        edgecolor=GRID_COLOR,
        linewidth=1.1,
        zorder=2,
    )
    _annotate_o_stone(ax, *o_cell)

    for row, column in admissible:
        ax.text(
            column - 0.5,
            row - 0.5,
            r"$A$",
            ha="center",
            va="center",
            fontsize=18,
            color=ADMISSIBLE_LABEL_COLOR,
            fontweight="bold",
            zorder=5,
        )

    # Draw an "x" over each crossed-out corner to show it has been ruled out.
    for row, column in crossed:
        x0, y0 = column - 1, row - 1

        ax.plot(
            [x0 + 0.18, x0 + 0.82],
            [y0 + 0.18, y0 + 0.82],
            color="#555555",
            linewidth=2.2,
            zorder=5,
        )

        ax.plot(
            [x0 + 0.18, x0 + 0.82],
            [y0 + 0.82, y0 + 0.18],
            color="#555555",
            linewidth=2.2,
            zorder=5,
        )

    label_H(ax)
    clean_axes(ax)

    fig.subplots_adjust(left=0, right=adjust_right, top=0.96, bottom=0.055)

    save_figure(fig, path, dpi=450, pad_inches=0.0)


def draw_tiebreak_inside_panel(path):
    """Tie-break when x_{n-2} lies inside H: only two cells are admissible."""
    _draw_tiebreak_panel(
        path,
        o_cell=(4, 4),
        x_cells=[(1, 1), (2, 2), (3, 3)],
        admissible={(5, 4), (4, 5)},
        crossed={(5, 5)},
        adjust_right=0.8,
    )


def draw_tiebreak_outside_panel(path):
    """Tie-break when x_{n-2} lies outside H: all four corners are admissible."""
    _draw_tiebreak_panel(
        path,
        o_cell=(3, 3),
        # X_2 and X_3 are moved off (3,3) so they do not collide with O.
        x_cells=[(1, 1), (2, 3), (3, 2)],
        admissible={(4, 4), (4, 5), (5, 4), (5, 5)},
        crossed=set(),
        adjust_right=0.75,
    )


def draw_claim_a_panel(path):
    """Panel (b): the intersection argument in Claim A."""
    n = 5

    L1 = {(4, c) for c in range(1, n + 1)} | {(r, 5) for r in range(1, n + 1)}
    L2 = {(5, c) for c in range(1, n + 1)} | {(r, 4) for r in range(1, n + 1)}
    intersection = L1 & L2

    fig, ax = _new_claims_axes()

    for row, column in L1:
        fill_cell(ax, row, column, facecolor=L1_COLOR, zorder=0)

    for row, column in L2 - intersection:
        fill_cell(ax, row, column, facecolor=L2_COLOR, zorder=0.5)

    for row, column in intersection:
        fill_cell(ax, row, column, facecolor=INTERSECTION_COLOR, zorder=0.7)

    draw_grid(ax, n, linewidth=0.9)

    fill_region(
        ax,
        (4, 5),
        (4, 5),
        facecolor="none",
        edgecolor="#555555",
        linewidth=2.0,
        zorder=2,
    )

    _annotate_o_stone(ax, 4, 4, fontsize=21, zorder=5)

    ax.text(
        4.5,
        4.5,
        r"$?$",
        ha="center",
        va="center",
        fontsize=27,
        color="#111111",
        fontweight="bold",
        zorder=5,
    )

    label_H(ax)

    ax.legend(
        handles=[
            mpatches.Patch(facecolor=L1_COLOR, edgecolor="none", label=r"$L_1$"),
            mpatches.Patch(facecolor=L2_COLOR, edgecolor="none", label=r"$L_2$"),
            mpatches.Patch(
                facecolor=INTERSECTION_COLOR,
                edgecolor="none",
                label=r"$L_1\cap L_2\subseteq H$",
            ),
        ],
        loc="center left",
        bbox_to_anchor=(0.85, 0.50),
        frameon=False,
        fontsize=10.5,
        handlelength=1.4,
        handleheight=1.0,
        borderaxespad=0.0,
        labelspacing=0.8,
    )

    clean_axes(ax)

    fig.subplots_adjust(left=0.04, right=0.88, top=0.96, bottom=0.055)

    save_figure(fig, path, dpi=450, pad_inches=0.03)


def draw_claim_aprime_panel(path):
    """Panel (c): the conclusion of Claim A'."""
    n = 5

    A = {1, 2, 3}
    B = {1, 2, 3}
    F = {(1, 2), (2, 3), (3, 1)}

    fig, ax = _new_claims_axes(xlim=(-0.75, 6.35), ylim=(5.48, -0.75))

    fill_region(
        ax,
        (1, 3),
        (1, 3),
        facecolor=AXB_COLOR,
        edgecolor="#555555",
        linewidth=1.8,
    )

    fill_region(ax, (4, 5), (4, 5), facecolor=LIGHT_GRAY)

    draw_grid(ax, n)

    for row, column in F:
        ax.add_patch(
            mpatches.Rectangle(
                (column - 1 + 0.08, row - 1 + 0.08),
                0.84,
                0.84,
                facecolor=PLAYER_STYLE["O"][1],
                edgecolor=O_COLOR,
                linewidth=1.8,
                zorder=2,
            )
        )

        ax.text(
            column - 0.5,
            row - 0.5,
            r"$F$",
            ha="center",
            va="center",
            fontsize=12,
            color=O_COLOR,
            fontweight="bold",
            zorder=3,
        )

    _annotate_o_stone(ax, 3, 3, fontsize=21, label_fontsize=9.5, zorder=5)

    ax.text(1.5, -0.28, r"$B$", ha="center", va="bottom", fontsize=15, fontweight="bold")
    ax.text(-0.28, 1.5, r"$A$", ha="right", va="center", fontsize=15, fontweight="bold")

    label_H(ax)

    ax.legend(
        handles=[
            mpatches.Patch(
                facecolor=AXB_COLOR, edgecolor="#555555", label=r"$A\times B$"
            ),
            mpatches.Patch(facecolor=LIGHT_GRAY, edgecolor="none", label=r"$H$"),
        ],
        loc="center left",
        bbox_to_anchor=(0.85, 0.45),
        frameon=False,
        fontsize=11,
        handlelength=1.4,
        handleheight=1.0,
        borderaxespad=0.0,
        labelspacing=0.8,
    )

    tick_rows(ax, A)
    tick_columns(ax, B)

    clean_axes(ax)

    fig.subplots_adjust(left=0.08, right=0.88, top=0.96, bottom=0.055)

    save_figure(fig, path, dpi=450, pad_inches=0.03)


def draw_tiebreak_claims_figure(output_dir=OUTDIR):
    """
    Draw four panels illustrating the tie-break and Claims A, A'.

    (a-i)  the 2x2 open block H when O's stone x_{n-2} lies inside H;
    (a-ii) the same when x_{n-2} lies outside H;
    (b)    the intersection argument in Claim A;
    (c)    the conclusion of Claim A'.
    """
    os.makedirs(output_dir, exist_ok=True)

    panels = [
        (draw_tiebreak_inside_panel, "tiebreak_claims_ai.png"),
        (draw_tiebreak_outside_panel, "tiebreak_claims_aii.png"),
        (draw_claim_a_panel, "tiebreak_claims_b.png"),
        (draw_claim_aprime_panel, "tiebreak_claims_c.png"),
    ]

    for draw_panel, filename in panels:
        path = out(output_dir, filename)
        draw_panel(path)
        print(f"Wrote {path}")


# Lemma 1 alternating-path figure

def draw_lemma1_figure(output_dir=OUTDIR):
    """
    Draw three separate illustrations of the alternating-path argument
    in Lemma 1 using a 4x4 bipartite graph.
    """
    os.makedirs(output_dir, exist_ok=True)

    n = 4

    p = 1
    q = 4

    M1 = {(2, 1), (3, 2), (4, 3)}
    M2 = {(1, 1), (2, 2), (4, 3)}

    P_edges_M1 = {(2, 1), (3, 2)}
    P_edges_M2 = {(1, 1), (2, 2)}

    switched = (M2 - P_edges_M2) | P_edges_M1

    def setup_graph_axis(ax):
        """Configure the shared bipartite-graph axis layout for this figure."""
        ax.set_xlim(-0.82, 1.72)
        ax.set_ylim(0.55, n + 0.92)
        ax.set_aspect("equal")
        ax.axis("off")

        for x, label_x, prefix, ha in [
            (0, -0.16, "r", "right"),
            (1, 1.16, "c", "left"),
        ]:
            for i in range(1, n + 1):
                ax.scatter(
                    x,
                    n + 1 - i,
                    s=135,
                    facecolor="white",
                    edgecolor="#222222",
                    linewidth=1.8,
                    zorder=5,
                )

                ax.text(
                    label_x,
                    n + 1 - i,
                    rf"${prefix}_{i}$",
                    ha=ha,
                    va="center",
                    fontsize=12,
                )

    def draw_edge(ax, edge, color, linewidth=2.4, linestyle="-", zorder=2):
        """Draw a single edge between a row vertex and a column vertex."""
        r, c = edge

        ax.plot(
            [0, 1],
            [n + 1 - r, n + 1 - c],
            color=color,
            linewidth=linewidth,
            linestyle=linestyle,
            solid_capstyle="round",
            zorder=zorder,
        )

    def annotate_vertex(ax, x, vertex, text, above):
        """Label a vertex with a short text callout above or below it."""
        offset = 0.36 if above else -0.36

        ax.annotate(
            text,
            xy=(x, n + 1 - vertex),
            xytext=(x, n + 1 - vertex + offset),
            ha="center",
            va="bottom" if above else "top",
            fontsize=11,
            fontweight="bold",
        )

    # Panel (a): the two matchings and the alternating path P

    fig, ax = plt.subplots(figsize=(4.7, 3.55))

    setup_graph_axis(ax)

    for edge in M1:
        draw_edge(ax, edge, X_COLOR, linewidth=2.8, zorder=3)

    for edge in M2:
        draw_edge(ax, edge, O_COLOR, linewidth=2.8, zorder=3)

    for edge in P_edges_M1 | P_edges_M2:
        draw_edge(ax, edge, "black", linewidth=1.9, linestyle=":", zorder=4)

    annotate_vertex(ax, 0, p, "$p$ exposed by $M_1$", above=True)
    annotate_vertex(ax, 1, q, "$q$ exposed by $M_2$", above=False)

    for color, linewidth, linestyle, label in [
        (X_COLOR, 2.8, "-", "$M_1$"),
        (O_COLOR, 2.8, "-", "$M_2$"),
        ("black", 1.9, ":", "$P$"),
    ]:
        ax.plot([], [], color=color, linewidth=linewidth, linestyle=linestyle, label=label)

    ax.legend(
        loc="center left",
        bbox_to_anchor=(1.015, 0.50),
        ncol=1,
        frameon=False,
        fontsize=11,
        handlelength=2.2,
        labelspacing=0.8,
        borderaxespad=0.0,
    )

    fig.subplots_adjust(left=0.12, right=0.69, top=0.91, bottom=0.04)

    save_figure(
        fig, out(output_dir, "lemma1_a.png"), dpi=400, pad_inches=0.02, announce=True
    )

    # Panel (b): after switching along P

    fig, ax = plt.subplots(figsize=(3.65, 3.55))

    setup_graph_axis(ax)

    for edge in switched:
        draw_edge(ax, edge, X_COLOR, linewidth=3.2, zorder=3)

    annotate_vertex(ax, 0, p, "$p$ exposed", above=True)
    annotate_vertex(ax, 1, q, "$q$ exposed", above=False)

    fig.subplots_adjust(left=0.12, right=0.88, top=0.91, bottom=0.04)

    save_figure(
        fig, out(output_dir, "lemma1_b.png"), dpi=400, pad_inches=0.02, announce=True
    )

    # Panel (c): the augmented matching

    fig, ax = plt.subplots(figsize=(3.65, 3.55))

    setup_graph_axis(ax)
    ax.set_xlim(-0.18, 1.18)

    for edge in switched:
        draw_edge(ax, edge, X_COLOR, linewidth=3.1, zorder=3)

    draw_edge(ax, (p, q), "black", linewidth=3.7, zorder=4)

    fig.subplots_adjust(left=0.02, right=0.98, top=0.91, bottom=0.04)

    save_figure(
        fig, out(output_dir, "lemma1_c.png"), dpi=400, pad_inches=0.02, announce=True
    )


# Lemma 3 four-panel figure

def draw_lemma3_figure(output_dir=OUTDIR):
    """Draw a compact four-panel matrix-style illustration of Lemma 3."""
    os.makedirs(output_dir, exist_ok=True)

    n = 5
    b = d = 5
    r, s = 1, 2

    def sigma(x):
        """Identity permutation used for this concrete example."""
        return x

    cases = [
        {"added": [(b, sigma(r))], "DR": {b, r}, "DC": {d}},
        {"added": [(r, d)], "DR": {b}, "DC": {d, sigma(r)}},
        {"added": [(b, sigma(r)), (s, d)], "DR": {b, r}, "DC": {d, sigma(s)}},
        {"added": [(r, d), (b, sigma(s))], "DR": {b, s}, "DC": {d, sigma(r)}},
    ]

    fig, axes = plt.subplots(1, 4, figsize=(8.6, 2.55))

    for ax, case, label in zip(axes, cases, ["(a)", "(b)", "(c)", "(d)"]):
        setup_board_axes(
            ax, n, xlim=(-0.35, n + 0.35), ylim=(n + 0.35, -0.35)
        )

        for row in case["DR"]:
            for col in case["DC"]:
                fill_cell(
                    ax,
                    row,
                    col,
                    facecolor="#f3f4f6",
                    edgecolor="#555555",
                    linewidth=1.4,
                    linestyle="--",
                    zorder=0,
                )

        draw_grid(ax, n, color="#b8b8b8", linewidth=0.65)

        # The existing matching, drawn as small solid dots.
        for i in range(1, n):
            ax.scatter(
                i - 0.5, i - 0.5, s=27, facecolor="#555555", edgecolor="none", zorder=4
            )

        # The cells added in this case, drawn as ringed dots.
        for row, col in case["added"]:
            x, y = col - 0.5, row - 0.5

            ax.scatter(
                x,
                y,
                s=70,
                facecolor="white",
                edgecolor="#111111",
                linewidth=1.7,
                zorder=5,
            )
            ax.scatter(x, y, s=13, facecolor="#111111", edgecolor="none", zorder=6)

        tick_rows(ax, case["DR"], length=0.22, zorder=6)
        tick_columns(ax, case["DC"], length=0.22, zorder=6)

        clean_axes(ax)

        ax.text(
            0.5,
            -0.10,
            label,
            transform=ax.transAxes,
            ha="center",
            va="top",
            fontsize=12,
        )

    fig.subplots_adjust(
        left=0.02, right=0.98, top=0.98, bottom=0.02, wspace=0.16
    )

    save_figure(
        fig,
        out(output_dir, "lemma3_cases.png"),
        dpi=400,
        pad_inches=0.03,
        announce=True,
    )


# Phase 2 forcing example

def make_phase2_example():
    """
    Construct the concrete 5x5 example used to illustrate Lemma 3 and
    the Phase 2 forcing mechanism.
    """
    matching = [("X", 1, 1), ("X", 2, 2), ("X", 3, 3), ("X", 4, 4)]

    single_threat = matching + [
        ("O", 5, 5),
        ("X", 5, 1),
        ("O", 1, 5),
    ]

    double_threat = single_threat + [("X", 2, 5)]

    return {
        "matching": matching,
        "single_threat": single_threat,
        "double_threat": double_threat,
    }


def generate_phase2_examples(output_dir=OUTDIR):
    """Generate three boards illustrating the Phase 2 forcing mechanism."""
    os.makedirs(output_dir, exist_ok=True)

    n = 5
    examples = make_phase2_example()

    boards = [
        ("matching", "phase2_1_matching.png", {(5, 5)}),
        ("single_threat", "phase2_2_single_threat.png", {(1, 5)}),
        ("double_threat", "phase2_3_double_threat.png", {(1, 2), (5, 2)}),
    ]

    for key, filename, threats in boards:
        draw_phase2_board(
            examples[key], n, out(output_dir, filename), threat_cells=threats
        )

    print(f"Wrote Phase 2 examples to {output_dir}/")


# Claim C case figures

def draw_claim_c_cases_figure(output_dir=OUTDIR):
    """
    Draw three separate boards illustrating the three cases in Claim C.

    The boards show representative positions at the point where O's
    forced move (b,d) is to be made.  The cell (b,d) is highlighted
    separately rather than counted as one of the displayed earlier
    O-stones.

    Case 1:  O's earlier stones meet column d.
    Case 2:  O's earlier stones meet row b but not column d.
    Case 3:  w = 0 and O's earlier stones form a matching inside A x B.

    The figures contain no explicit F labels and no legends.
    """
    os.makedirs(output_dir, exist_ok=True)

    n = 5

    # X owns an (n-1)-matching after the tie-break, so b = 4 and d = 5,
    # and the open block H is rows {4,5} x columns {4,5}.
    x_cells = [(1, 1), (2, 2), (3, 3), (5, 4)]

    b = 4
    d = 5

    def draw_case(o_cells, path, show_axb=False):
        """Draw one Claim C case board for the given set of O stones."""
        fig, ax = plt.subplots(figsize=(4.35, 4.35))

        # Leave a little extra room below/left for labels.
        setup_board_axes(
            ax, n, xlim=(-0.48, n + 0.18), ylim=(n + 0.30, -0.55)
        )

        # Structural shading: row b and column d in every case.
        ax.add_patch(
            mpatches.Rectangle(
                (0, b - 1), n, 1, facecolor="#cccccc", edgecolor="none", zorder=0
            )
        )
        ax.add_patch(
            mpatches.Rectangle(
                (d - 1, 0), 1, n, facecolor="#cccccc", edgecolor="none", zorder=0
            )
        )

        if show_axb:
            fill_region(
                ax,
                (1, 3),
                (1, 3),
                facecolor=AXB_COLOR,
                edgecolor="#555555",
                linewidth=1.5,
            )

        # The open block H, outlined in front of everything else.
        fill_region(
            ax,
            (4, 5),
            (4, 5),
            facecolor="none",
            edgecolor="red",
            linewidth=2.2,
            linestyle="--",
            zorder=5,
        )

        ax.text(
            4.0,
            n + 0.12,
            r"$H$",
            ha="center",
            va="top",
            fontsize=18,
            color="red",
            fontweight="bold",
            zorder=6,
        )

        if show_axb:
            # A = B = {1,2,3}; small dots indicate membership.
            for row in range(1, 4):
                ax.plot(
                    -0.16,
                    row - 0.5,
                    marker="o",
                    markersize=4.5,
                    color="#555555",
                    markeredgewidth=0,
                    zorder=5,
                )

            ax.text(
                -0.38,
                1.5,
                r"$A$",
                ha="center",
                va="center",
                fontsize=18,
                fontweight="bold",
                zorder=5,
            )

            for col in range(1, 4):
                ax.plot(
                    col - 0.5,
                    -0.16,
                    marker="o",
                    markersize=4.5,
                    color="#555555",
                    markeredgewidth=0,
                    zorder=5,
                )

            ax.text(
                1.5,
                -0.38,
                r"$B$",
                ha="center",
                va="center",
                fontsize=18,
                fontweight="bold",
                zorder=5,
            )

        draw_grid(ax, n)

        draw_numbered_stones(ax, x_cells, "X", fontsize=21)
        draw_numbered_stones(ax, o_cells, "O", fontsize=21)

        # (b,d) is not an O stone yet, so mark it as a forced move.
        draw_target(ax, b, d)

        clean_axes(ax)

        fig.subplots_adjust(left=0.02, right=0.98, top=0.98, bottom=0.02)

        save_figure(fig, path, dpi=450, pad_inches=0.02, announce=True)

    cases = [
        # Case 1: O's earlier stones meet column d.
        ([(1, 5), (2, 4), (3, 1)], "claim_c_i.png", False),
        # Case 2: O's earlier stones meet row b but not column d.
        ([(4, 1), (2, 4), (3, 2)], "claim_c_ii.png", False),
        # Case 3: w = 0, with A = B = {1,2,3}.
        ([(1, 2), (2, 3), (3, 1)], "claim_c_iii.png", True),
    ]

    for o_cells, filename, show_axb in cases:
        draw_case(o_cells, out(output_dir, filename), show_axb=show_axb)


# Two-live-rows figures

def draw_two_live_rows_figure(output_dir=OUTDIR):
    """
    Draw two figures showing the same Phase-2 position with two live rows.

    The first highlights row r, the second row s.  A row t is live when
    both (t, d) and (b, sigma(t)) are free.

    In the concrete example n = 5, b = d = 5, sigma is the identity,
    r = 1 and s = 2, so r is live because (1,5) and (5,1) are free, and
    s is live because (2,5) and (5,2) are free.  The cell (b,d) = (5,5)
    is marked separately as the forced cell.
    """
    os.makedirs(output_dir, exist_ok=True)

    n = 5

    # X owns the (n-1)-matching (1,1), (2,2), (3,3), (4,4), so b = d = 5
    # and sigma is the identity.  O's earlier stones are placed away from
    # the four cells relevant to the two live rows.
    x_cells = [(1, 1), (2, 2), (3, 3), (4, 4)]
    o_cells = [(1, 3), (2, 4), (3, 1)]

    b = d = 5
    r, s = 1, 2

    def sigma(t):
        """Identity permutation used for this concrete example."""
        return t

    # Sanity checks for the intended example.
    occupied = set(x_cells) | set(o_cells)

    for t in (r, s):
        assert (t, d) not in occupied
        assert (b, sigma(t)) not in occupied

    assert (b, d) not in occupied

    LIVE_COLOR = "#b7e4c7"
    LIVE_EDGE = "#2f6f44"
    FORCED_COLOR = "#555555"

    def draw_panel(ax, live_row, live_name):
        """Draw one board emphasizing the two witness cells for live_row."""
        setup_board_axes(
            ax, n, xlim=(-0.62, n + 0.42), ylim=(n + 0.58, -0.62)
        )

        # Highlight only the two cells witnessing that the row is live.
        witness_cells = {(live_row, d), (b, sigma(live_row))}

        for row, column in witness_cells:
            fill_cell(
                ax,
                row,
                column,
                facecolor=LIVE_COLOR,
                edgecolor=LIVE_EDGE,
                linewidth=2.5,
                zorder=1.5,
            )

        draw_grid(ax, n, zorder=2)

        draw_numbered_stones(ax, x_cells, "X", fontsize=21, zorder=3)
        draw_numbered_stones(ax, o_cells, "O", fontsize=21, zorder=3)

        draw_target(ax, b, d, color=FORCED_COLOR)

        ax.text(
            d - 0.5,
            d + 0.25,
            r"$(b,d)$",
            ha="center",
            va="top",
            fontsize=12.5,
            color=FORCED_COLOR,
            fontweight="bold",
            clip_on=False,
            zorder=8,
        )

        # Label the live row to the left of the board.
        tick_rows(ax, [live_row], color=LIVE_EDGE, linewidth=2.2, length=0.20, zorder=6)

        ax.text(
            -0.28,
            live_row - 0.5,
            rf"${live_name}$",
            ha="right",
            va="center",
            fontsize=17,
            color=LIVE_EDGE,
            fontweight="bold",
            clip_on=False,
            zorder=7,
        )

        # Label the two witness cells.
        ax.text(
            d - 0.5,
            live_row - 0.5,
            rf"$({live_name},d)$",
            ha="center",
            va="center",
            fontsize=9.5,
            color=LIVE_EDGE,
            fontweight="bold",
            zorder=8,
        )

        ax.text(
            sigma(live_row) - 0.5,
            b - 0.5,
            rf"$(b,\sigma({live_name}))$",
            ha="center",
            va="center",
            fontsize=9.0,
            color=LIVE_EDGE,
            fontweight="bold",
            zorder=8,
        )

        clean_axes(ax)

    for live_row, live_name, filename in [
        (r, "r", "two_live_rows_r.png"),
        (s, "s", "two_live_rows_s.png"),
    ]:
        fig, ax = plt.subplots(figsize=(4.1, 4.15))

        draw_panel(ax, live_row, live_name)

        fig.subplots_adjust(left=0.07, right=0.98, top=0.98, bottom=0.08)

        save_figure(
            fig,
            out(output_dir, filename),
            dpi=450,
            pad_inches=0.03,
            announce=True,
        )


# Example registry

def generate_example(name, moves, n, output_dir=OUTDIR):
    """Save one example's board and history."""
    os.makedirs(output_dir, exist_ok=True)

    result = validate_history(moves, n)

    board_path = out(output_dir, f"example_{name}_{n}x{n}.png")
    csv_path = out(output_dir, f"example_{name}_{n}x{n}.csv")

    draw_board(moves, n, board_path, highlight_final=result in ("X", "O"))
    save_history_csv(moves, csv_path)

    print(f"Wrote {board_path}")
    print(f"Wrote {csv_path}")

    return {
        "outcome": result,
        "board": board_path,
        "history": csv_path,
        "moves": moves,
    }


# Main

def main():
    """Regenerate every example figure and CSV in the output directory."""
    n = 5

    os.makedirs(OUTDIR, exist_ok=True)

    # Examples 1-3: a decisive game for each player, plus a draw.
    generate_example("win", make_x_win(n), n)
    generate_example("loss", make_o_win(n), n)
    generate_example("draw", make_draw(n), n)

    # Example 4: Phase 1 open-block invariant.
    draw_phase1_invariant_figure()

    # Example 5: Phase 2 forcing mechanism.
    generate_phase2_examples()

    # Example 6: Lemma 3 cases (a)--(d).
    draw_lemma3_figure()

    # Example 7: Lemma 1 alternating-path argument.
    draw_lemma1_figure()

    # Example 8: tie-break, Claim A, Claim A', and the Claim C cases.
    draw_tiebreak_claims_figure()
    draw_claim_c_cases_figure()

    # Example 9: two live rows.
    draw_two_live_rows_figure()

    print()
    print("Done.")


if __name__ == "__main__":
    main()