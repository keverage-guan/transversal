"""
Interactive transversal achievement game.

Usage:
    python3 transversal_play.py --n 4
    python3 transversal_play.py --n 5

Click cells to alternate X/O moves.
"""

from __future__ import annotations

import argparse
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches


X_COLOR = "#2b6cb0"
O_COLOR = "#c53030"
GRID_COLOR = "#333333"


class Game:
    def __init__(self, n):
        self.n = n
        self.board = [[None for _ in range(n)] for _ in range(n)]
        self.moves = []

        self.count = {
            "X": 0,
            "O": 0
        }

        self.turn = "X"
        self.fig, self.ax = plt.subplots(figsize=(1.1*n+1, 1.1*n+1))

        self.ax.set_xlim(0, n)
        self.ax.set_ylim(0, n)
        self.ax.set_aspect("equal")
        self.ax.invert_yaxis()

        for i in range(n+1):
            self.ax.plot(
                [0,n], [i,i],
                color=GRID_COLOR,
                lw=1.2
            )
            self.ax.plot(
                [i,i], [0,n],
                color=GRID_COLOR,
                lw=1.2
            )

        self.ax.set_xticks([])
        self.ax.set_yticks([])

        for spine in self.ax.spines.values():
            spine.set_visible(False)

        self.ax.set_title(
            f"n={n}: X's turn",
            fontsize=12
        )

        self.fig.canvas.mpl_connect(
            "button_press_event",
            self.click
        )

    def click(self, event):
        if event.inaxes != self.ax:
            return

        c = int(event.xdata)
        r = int(event.ydata)

        if not (0 <= r < self.n and 0 <= c < self.n):
            return

        if self.board[r][c] is not None:
            return

        self.play(r, c)

    def play(self, r, c):

        who = self.turn

        self.count[who] += 1
        label_num = self.count[who]

        self.board[r][c] = who

        self.moves.append(
            (
                who,
                [r+1, c+1],
                len(self.moves)+1
            )
        )

        face = "#dbeafe" if who == "X" else "#fde8e8"
        color = X_COLOR if who == "X" else O_COLOR

        rect = mpatches.Rectangle(
            (c,r),
            1,
            1,
            facecolor=face,
            edgecolor="none",
            zorder=2
        )

        self.ax.add_patch(rect)

        self.ax.text(
            c+0.5,
            r+0.5,
            rf"${who}_{{{label_num}}}$",
            ha="center",
            va="center",
            fontsize=13,
            color=color,
            fontweight="bold",
            zorder=3
        )

        if self.check_win():
            self.highlight_win()
            self.ax.set_title(
                f"X wins at ply {len(self.moves)}",
                fontsize=12
            )
            print("\nWinning sequence:")
            print(self.moves)
            return

        self.turn = "O" if self.turn == "X" else "X"

        self.ax.set_title(
            f"n={self.n}: {self.turn}'s turn",
            fontsize=12
        )

        self.fig.canvas.draw_idle()


    def check_win(self):
        rowmask = [0] * self.n

        for r in range(self.n):
            for c in range(self.n):
                if self.board[r][c] == "X":
                    rowmask[r] |= 1 << c

        if max_matching(tuple(rowmask), self.n)[0] == self.n:
            self.winning_cells = self.winning_transversal()
            return True

        return False


    def winning_transversal(self):

        rowmask = [0] * self.n

        for r in range(self.n):
            for c in range(self.n):
                if self.board[r][c] == "X":
                    rowmask[r] |= 1 << c

        size, match_row, match_col = max_matching(
            rowmask,
            self.n
        )

        if size != self.n:
            return None

        return [
            (r, match_row[r])
            for r in range(self.n)
        ]

    def highlight_win(self):

        cells = self.winning_transversal()

        for r,c in cells:
            rect = mpatches.Rectangle(
                (c,r),
                1,
                1,
                fill=False,
                edgecolor="black",
                linewidth=3,
                zorder=4
            )
            self.ax.add_patch(rect)

        self.fig.canvas.draw_idle()

def max_matching(rowmask, n):
    match_row = [-1] * n
    match_col = [-1] * n
    size = 0

    for r in range(n):
        if try_augment(r, rowmask, match_row, match_col, n, [False]*n):
            size += 1

    return size, match_row, match_col


def try_augment(r, rowmask, match_row, match_col, n, seen):

    m = rowmask[r]
    c = 0

    while m:
        if m & 1:
            if not seen[c]:
                seen[c] = True

                if match_col[c] == -1 or try_augment(
                    match_col[c],
                    rowmask,
                    match_row,
                    match_col,
                    n,
                    seen
                ):
                    match_col[c] = r
                    match_row[r] = c
                    return True

        m >>= 1
        c += 1

    return False

def main():

    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--n",
        type=int,
        required=True
    )

    args = parser.parse_args()

    game = Game(args.n)

    plt.show()


if __name__ == "__main__":
    main()