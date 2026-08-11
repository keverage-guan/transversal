from __future__ import annotations

import os
from itertools import permutations

import matplotlib
matplotlib.use("Agg")

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches


# =====================================================================
# Configuration
# =====================================================================

OUTDIR = "playthrough_6x6"
N = 6

X_COLOR = "#2b6cb0"
O_COLOR = "#c53030"
GRID_COLOR = "#333333"

LIGHT_GRAY = "#d9d9d9"

ADMISSIBLE_COLOR = "#b7e4c7"
LIVE1_COLOR = "#b7e4c7"
LIVE1_EDGE = "#2f6f44"

LIVE2_COLOR = "#f6d6a8"
LIVE2_EDGE = "#9a5f13"

FORCED_COLOR = "#555555"


# =====================================================================
# Game utilities
# =====================================================================

def cells_for_player(moves, player):
    return {
        (r, c)
        for who, r, c in moves
        if who == player
    }


def has_transversal(moves, player, n):
    cells = cells_for_player(moves, player)

    for cols in permutations(range(1, n + 1)):
        if all(
            (r, cols[r - 1]) in cells
            for r in range(1, n + 1)
        ):
            return True

    return False


def winning_transversal(moves, player, n):
    cells = cells_for_player(moves, player)

    for cols in permutations(range(1, n + 1)):
        transversal = [
            (r, cols[r - 1])
            for r in range(1, n + 1)
        ]

        if all(cell in cells for cell in transversal):
            return transversal

    return None


def outcome(moves, n):
    x_wins = has_transversal(moves, "X", n)
    o_wins = has_transversal(moves, "O", n)

    if x_wins and o_wins:
        raise ValueError(
            "Invalid position: both players have transversals."
        )

    if x_wins:
        return "X"

    if o_wins:
        return "O"

    if len(moves) == n * n:
        return "draw"

    return "ongoing"


def validate_history(moves, n):
    occupied = set()

    for ply, (player, row, column) in enumerate(
        moves,
        start=1,
    ):
        expected_player = (
            "X" if ply % 2 == 1 else "O"
        )

        if player != expected_player:
            raise ValueError(
                f"Ply {ply}: expected {expected_player}, "
                f"got {player}."
            )

        if not (
            1 <= row <= n
            and 1 <= column <= n
        ):
            raise ValueError(
                f"Ply {ply}: ({row}, {column}) "
                "is outside the board."
            )

        if (row, column) in occupied:
            raise ValueError(
                f"Ply {ply}: ({row}, {column}) "
                "was already occupied."
            )

        occupied.add((row, column))

        if ply < len(moves):
            result = outcome(moves[:ply], n)

            if result != "ongoing":
                raise ValueError(
                    f"Game ended at ply {ply} "
                    f"with outcome {result}."
                )

    if outcome(moves, n) != "X":
        raise ValueError(
            "The prescribed playthrough does not end with X winning."
        )


# =====================================================================
# Open block H
# =====================================================================

def get_H(ply):
    """
    Return the actual open block H after the given ply.

    H = U_R x U_C, where U_R and U_C are the rows and columns
    not yet used by X.
    """

    x_cells = {
        (row, column)
        for player, row, column in FULL_GAME[:ply]
        if player == "X"
    }

    used_rows = {
        row
        for row, _ in x_cells
    }

    used_cols = {
        column
        for _, column in x_cells
    }

    open_rows = set(range(1, N + 1)) - used_rows
    open_cols = set(range(1, N + 1)) - used_cols

    return open_rows, open_cols


# =====================================================================
# Special annotations
# =====================================================================

def annotations_for_ply(ply):
    """
    Return cells that should be specially highlighted.

    Threats are represented only by target marks.

    This playthrough follows Plan (i):
        X_6 = (b, sigma(r)) = (6,1)
        O_6 = (r,d)         = (1,5)
        X_7 = (s,d)         = (2,5)
        double threat:
            (b,sigma(s))    = (6,3)
            (r,sigma(s))    = (1,3)
    """

    # -------------------------------------------------------------
    # O_4 enters H.
    #
    # H = {5,6} x {5,6}.
    #
    # The two admissible cells are (5,6) and (6,5).
    # -------------------------------------------------------------

    if ply == 8:
        return {
            "admissible": {
                (5, 6),
                (6, 5),
            },
            "live_1": set(),
            "live_2": set(),
            "forced": set(),
        }

    # -------------------------------------------------------------
    # X_5 chooses (5,6).
    #
    # Highlight the remaining admissible square.
    # -------------------------------------------------------------

    if ply == 9:
        return {
            "admissible": {
                (6, 5),
            },
            "live_1": set(),
            "live_2": set(),
            "forced": {(6, 5)},
        }

    # -------------------------------------------------------------
    # O_5 blocks (6,5).
    #
    # The two live rows are:
    #
    #   r = 1:
    #       (1,5) and (6,1)
    #
    #   s = 2:
    #       (2,5) and (6,3)
    #
    # We use Plan (i).
    # -------------------------------------------------------------

    if ply == 10:
        return {
            "admissible": set(),
            "live_1": {
                (1, 5),
                (6, 1),
            },
            "live_2": {
                (2, 5),
                (6, 3),
            },
            "forced": set(),
        }

    # -------------------------------------------------------------
    # X_6 plays (6,1) = (b, sigma(r)).
    #
    # This creates the unique threat (1,5) = (r,d).
    # -------------------------------------------------------------

    if ply == 11:
        return {
            "admissible": set(),
            "live_1": {
                (6, 1),
            },
            "live_2": set(),
            "forced": {(1, 5)},
        }

    # -------------------------------------------------------------
    # O_6 blocks (1,5).
    #
    # The second live row remains:
    #
    #     (2,5) and (6,3)
    # -------------------------------------------------------------

    if ply == 12:
        return {
            "admissible": set(),
            "live_1": set(),
            "live_2": {
                (2, 5),
                (6, 3),
            },
            "forced": set(),
        }

    # -------------------------------------------------------------
    # X_7 plays (2,5) = (s,d).
    #
    # This creates the double threat:
    #
    #     (6,3) = (b, sigma(s))
    #     (1,3) = (r, sigma(s))
    # -------------------------------------------------------------

    if ply == 13:
        return {
            "admissible": set(),
            "live_1": set(),
            "live_2": set(),
            "forced": {
                (6, 3),
                (1, 3),
            },
        }

    # -------------------------------------------------------------
    # O_7 blocks (6,3).
    #
    # The remaining threat is (1,3).
    # -------------------------------------------------------------

    if ply == 14:
        return {
            "admissible": set(),
            "live_1": set(),
            "live_2": set(),
            "forced": {(1, 3)},
        }

    # -------------------------------------------------------------
    # X_8 plays (1,3) and wins.
    # -------------------------------------------------------------

    if ply == 15:
        return {
            "admissible": set(),
            "live_1": set(),
            "live_2": set(),
            "forced": set(),
        }

    # -------------------------------------------------------------
    # Default.
    # -------------------------------------------------------------

    return {
        "admissible": set(),
        "live_1": set(),
        "live_2": set(),
        "forced": set(),
    }


# =====================================================================
# Drawing helpers
# =====================================================================

def draw_H(ax, open_rows, open_cols):
    """
    Shade the cells of H and draw a dotted outer boundary
    around each connected rectangular component of H.
    """

    if not open_rows or not open_cols:
        return

    # -------------------------------------------------------------
    # Shade each actual cell of H.
    # -------------------------------------------------------------

    for row in open_rows:
        for col in open_cols:
            ax.add_patch(
                mpatches.Rectangle(
                    (col - 1, row - 1),
                    1,
                    1,
                    facecolor=LIGHT_GRAY,
                    edgecolor="none",
                    alpha=0.72,
                    zorder=0,
                )
            )

    # -------------------------------------------------------------
    # Find consecutive runs of rows and columns.
    # -------------------------------------------------------------

    def consecutive_runs(values):
        values = sorted(values)

        if not values:
            return []

        runs = []

        start = values[0]
        previous = values[0]

        for value in values[1:]:
            if value == previous + 1:
                previous = value
            else:
                runs.append((start, previous))
                start = value
                previous = value

        runs.append((start, previous))

        return runs

    row_runs = consecutive_runs(open_rows)
    col_runs = consecutive_runs(open_cols)

    # -------------------------------------------------------------
    # Draw dotted boundary around every component.
    # -------------------------------------------------------------

    for r_min, r_max in row_runs:
        for c_min, c_max in col_runs:

            width = c_max - c_min + 1
            height = r_max - r_min + 1

            ax.add_patch(
                mpatches.Rectangle(
                    (c_min - 1, r_min - 1),
                    width,
                    height,
                    facecolor="none",
                    edgecolor="#555555",
                    linewidth=2.0,
                    linestyle=":",
                    zorder=5,
                )
            )


def highlight_cell(
    ax,
    row,
    col,
    facecolor,
    edgecolor,
    linewidth=2.4,
):
    ax.add_patch(
        mpatches.Rectangle(
            (col - 1, row - 1),
            1,
            1,
            facecolor=facecolor,
            edgecolor=edgecolor,
            linewidth=linewidth,
            zorder=1.5,
        )
    )


def draw_target(ax, row, col):
    """
    Mark an empty special cell with a target.
    """

    x = col - 0.5
    y = row - 0.5

    ax.add_patch(
        mpatches.Circle(
            (x, y),
            radius=0.35,
            facecolor="none",
            edgecolor=FORCED_COLOR,
            linewidth=2.0,
            zorder=7,
        )
    )

    ax.add_patch(
        mpatches.Circle(
            (x, y),
            radius=0.16,
            facecolor="none",
            edgecolor=FORCED_COLOR,
            linewidth=1.6,
            zorder=7,
        )
    )

    ax.add_patch(
        mpatches.Circle(
            (x, y),
            radius=0.05,
            facecolor=FORCED_COLOR,
            edgecolor="none",
            zorder=8,
        )
    )


def draw_transversal(ax, transversal):
    """
    Put the black boundary highlight around every cell
    in the winning transversal.
    """

    for row, column in transversal:

        x0 = column - 1
        x1 = column

        y0 = row - 1
        y1 = row

        ax.plot(
            [x0, x1],
            [y0, y0],
            color="black",
            linewidth=3.2,
            solid_capstyle="butt",
            zorder=9,
            clip_on=False,
        )

        ax.plot(
            [x0, x1],
            [y1, y1],
            color="black",
            linewidth=3.2,
            solid_capstyle="butt",
            zorder=9,
            clip_on=False,
        )

        ax.plot(
            [x0, x0],
            [y0, y1],
            color="black",
            linewidth=3.2,
            solid_capstyle="butt",
            zorder=9,
            clip_on=False,
        )

        ax.plot(
            [x1, x1],
            [y0, y1],
            color="black",
            linewidth=3.2,
            solid_capstyle="butt",
            zorder=9,
            clip_on=False,
        )


# =====================================================================
# Draw one frame
# =====================================================================

def draw_board(moves, ply, path):

    fig, ax = plt.subplots(
        figsize=(5.0, 5.0),
    )

    ax.set_xlim(
        -0.20,
        N + 0.20,
    )

    ax.set_ylim(
        N + 0.20,
        -0.20,
    )

    ax.set_aspect("equal")

    # -------------------------------------------------------------
    # H
    # -------------------------------------------------------------

    open_rows, open_cols = get_H(ply)

    draw_H(
        ax,
        open_rows,
        open_cols,
    )

    # -------------------------------------------------------------
    # Special cells
    # -------------------------------------------------------------

    annotations = annotations_for_ply(ply)

    for row, col in annotations["admissible"]:
        highlight_cell(
            ax,
            row,
            col,
            ADMISSIBLE_COLOR,
            LIVE1_EDGE,
            linewidth=2.4,
        )

    for row, col in annotations["live_1"]:
        highlight_cell(
            ax,
            row,
            col,
            LIVE1_COLOR,
            LIVE1_EDGE,
            linewidth=2.5,
        )

    for row, col in annotations["live_2"]:
        highlight_cell(
            ax,
            row,
            col,
            LIVE2_COLOR,
            LIVE2_EDGE,
            linewidth=2.5,
        )

    # -------------------------------------------------------------
    # Grid
    # -------------------------------------------------------------

    for i in range(N + 1):

        ax.plot(
            [0, N],
            [i, i],
            color=GRID_COLOR,
            linewidth=1.0,
            zorder=3,
        )

        ax.plot(
            [i, i],
            [0, N],
            color=GRID_COLOR,
            linewidth=1.0,
            zorder=3,
        )

    # -------------------------------------------------------------
    # Stones
    # -------------------------------------------------------------

    move_numbers = {
        "X": 0,
        "O": 0,
    }

    occupied = set()

    for player, row, column in moves:

        move_numbers[player] += 1
        occupied.add((row, column))

        r0 = row - 1
        c0 = column - 1

        if player == "X":
            color = X_COLOR
            face = "#dbeafe"
        else:
            color = O_COLOR
            face = "#fde8e8"

        ax.add_patch(
            mpatches.Rectangle(
                (c0, r0),
                1,
                1,
                facecolor=face,
                edgecolor=GRID_COLOR,
                linewidth=1.1,
                zorder=4,
            )
        )

        ax.text(
            c0 + 0.5,
            r0 + 0.5,
            rf"${player}_{{{move_numbers[player]}}}$",
            ha="center",
            va="center",
            fontsize=22,
            color=color,
            fontweight="bold",
            zorder=6,
        )

    # -------------------------------------------------------------
    # Target marks for forced cells
    # -------------------------------------------------------------

    for row, col in annotations["forced"]:

        if (row, col) not in occupied:
            draw_target(
                ax,
                row,
                col,
            )

    # -------------------------------------------------------------
    # Final winning transversal
    # -------------------------------------------------------------

    if ply == len(FULL_GAME):

        transversal = winning_transversal(
            moves,
            "X",
            N,
        )

        if transversal is None:
            raise ValueError(
                "Final position has no X transversal."
            )

        draw_transversal(
            ax,
            transversal,
        )

    # -------------------------------------------------------------
    # Clean axes
    # -------------------------------------------------------------

    ax.set_xticks([])
    ax.set_yticks([])

    for spine in ax.spines.values():
        spine.set_visible(False)

    fig.subplots_adjust(
        left=0.02,
        right=0.98,
        top=0.98,
        bottom=0.02,
    )

    fig.savefig(
        path,
        dpi=450,
        bbox_inches="tight",
        pad_inches=0.02,
    )

    plt.close(fig)


# =====================================================================
# 6x6 playthrough
# =====================================================================

FULL_GAME = [

    # -------------------------------------------------------------
    # Phase 1
    #
    # X stones:
    #
    #   X_1 = (1,1)
    #   X_2 = (2,3)
    #   X_3 = (3,2)
    #   X_4 = (4,4)
    #
    # The first four rows and columns are exhausted, so
    # H becomes the contiguous 2x2 block {5,6} x {5,6}.
    # -------------------------------------------------------------

    ("X", 1, 1),       # X_1
    ("O", 1, 2),       # O_1

    ("X", 2, 3),       # X_2
    ("O", 3, 4),       # O_2

    ("X", 3, 2),       # X_3
    ("O", 4, 5),       # O_3

    ("X", 4, 4),       # X_4
    ("O", 5, 5),       # O_4: enters H

    # -------------------------------------------------------------
    # Tie-break
    # -------------------------------------------------------------

    ("X", 5, 6),       # X_5

    ("O", 6, 5),       # O_5

    # -------------------------------------------------------------
    # Phase 2 -- Plan (i)
    #
    # Here F meets column d=5, so the strategy uses Plan (i).
    #
    # r = 1, s = 2
    #
    # X_6 = (b, sigma(r)) = (6,1)
    # O_6 = (r,d)         = (1,5)
    # X_7 = (s,d)         = (2,5)
    #
    # X_7 creates the double threat:
    #   (b,sigma(s)) = (6,3)
    #   (r,sigma(s)) = (1,3)
    # -------------------------------------------------------------

    ("X", 6, 1),       # X_6
    ("O", 1, 5),       # O_6: forced block

    ("X", 2, 5),       # X_7
    ("O", 6, 3),       # O_7: blocks one of the double threats

    ("X", 1, 3),       # X_8: wins
]


# =====================================================================
# Main
# =====================================================================

def main():

    os.makedirs(
        OUTDIR,
        exist_ok=True,
    )

    validate_history(
        FULL_GAME,
        N,
    )

    print(
        "Validated: X wins on ply "
        f"{len(FULL_GAME)}."
    )

    print(
        "Winning transversal:",
        winning_transversal(
            FULL_GAME,
            "X",
            N,
        ),
    )

    for ply in range(
        1,
        len(FULL_GAME) + 1,
    ):

        path = os.path.join(
            OUTDIR,
            f"move_{ply:02d}.png",
        )

        draw_board(
            FULL_GAME[:ply],
            ply,
            path,
        )

        player, row, col = FULL_GAME[ply - 1]

        print(
            f"Wrote {path}: "
            f"{player} at ({row},{col})"
        )

    print()
    print(
        f"Done. Images written to {OUTDIR}/"
    )


if __name__ == "__main__":
    main()