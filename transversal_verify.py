#!/usr/bin/env python3
"""
transversal_verify.py
=====================

Exhaustive verification of the upper bound  "X wins by ply 2n+3"  for the
transversal achievement game on the n x n board.

The script implements the strategy of Section 4 of the accompanying note
(Phase-1 rule of Sec. 3, tie-break of Sec. 5, plan/pair rule 4.3, deviation
rule 4.4) and plays it against EVERY legal defence by O, checking at every
node the claims the proof asserts:

    (I)    open-block invariant: H = U_R x U_C contains no O-stone
           throughout Phase 1                                        [Lemma 4]
    (T)    after X's move n-1: (b,d) is free, X's stones are a matching of
           size n-1 missing row b and column d, and w <= n-3         [Sec. 5]
    (S)    X's moves at plies 2n-3 and 2n-1 leave exactly ONE free
           completing cell  (a single, forcing threat)          [Lemma 3(a,b)]
    (D)    X's move at ply 2n+1 leaves exactly TWO free completing cells
           (a genuine double threat)                            [Lemma 3(c,d)]
    (Ca)   O has no threat when X is to move at plies 2n-1 and 2n+1
                                                                  [Claim C(a)]
    (Cb)   no legal O move at plies 2n-2, 2n or 2n+2 completes a transversal
           for O                                                  [Claim C(b)]
    (W)    X completes a transversal at a ply <= 2n+3

Only the UPPER bound is verified.  Nothing here speaks to optimality of
2n+3; that is a separate (open) question.

Usage
-----
    python3 transversal_verify.py --n 4
    python3 transversal_verify.py --n 5 --outdir results
    python3 transversal_verify.py --n 4 --all-x-choices     # strategy CLASS
    python3 transversal_verify.py --selftest                # lemma checks

Author: (see accompanying note).  Public domain / CC0.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from collections import Counter, defaultdict
from functools import lru_cache
from multiprocessing import Pool, cpu_count

# ---------------------------------------------------------------------------
# Bipartite matching engine.
#
# A set S of cells is stored as a tuple of n row-masks: bit c of entry r is
# set iff (r,c) in S.  nu(S) is the maximum size of a matching inside S.
# ---------------------------------------------------------------------------


def max_matching(rowmask, n):
    """Kuhn's algorithm.  Returns (size, match_row, match_col) with
    match_row[r] = column matched to row r (or -1) and vice versa."""
    match_row = [-1] * n
    match_col = [-1] * n
    size = 0
    for r in range(n):
        seen = 0
        stack = [(r, 0)]
        # iterative DFS for an augmenting path from row r
        path = []
        if _try_augment(r, rowmask, match_row, match_col, n, [0]):
            size += 1
    return size, match_row, match_col


def _try_augment(r, rowmask, match_row, match_col, n, _dummy, seen=None):
    """Recursive augmenting-path search (n <= ~10, depth is tiny)."""
    if seen is None:
        seen = [False] * n
    m = rowmask[r]
    c = 0
    while m:
        if m & 1:
            if not seen[c]:
                seen[c] = True
                if match_col[c] == -1 or _try_augment(
                    match_col[c], rowmask, match_row, match_col, n, None, seen
                ):
                    match_col[c] = r
                    match_row[r] = c
                    return True
        m >>= 1
        c += 1
    return False


@lru_cache(maxsize=None)
def nu(rowmask, n):
    return max_matching(rowmask, n)[0]


def completing_cells(rowmask, n):
    """All cells f (occupied or not) with nu(S + f) = n.

    Implements Lemma 1: if nu(S) = n-1 the answer is the rectangle
    D_R x D_C, where D_R (resp. D_C) is the set of rows (columns) left
    exposed by SOME maximum matching, computed by alternating search from
    the row (column) exposed by one fixed maximum matching.  If nu(S) <= n-2
    the answer is empty.
    """
    size, match_row, match_col = max_matching(rowmask, n)
    if size <= n - 2:
        return []
    if size == n:
        return []  # already a transversal; nothing to "complete"

    p0 = next(r for r in range(n) if match_row[r] == -1)
    q0 = next(c for c in range(n) if match_col[c] == -1)

    # D_R: rows reachable from p0 by alternating (edge, matched edge) steps.
    DR = {p0}
    frontier = [p0]
    seen_cols = set()
    while frontier:
        r = frontier.pop()
        m = rowmask[r]
        c = 0
        while m:
            if (m & 1) and c not in seen_cols:
                seen_cols.add(c)
                r2 = match_col[c]
                # r2 == -1 would be an augmenting path, impossible at maximum
                if r2 != -1 and r2 not in DR:
                    DR.add(r2)
                    frontier.append(r2)
            m >>= 1
            c += 1

    # D_C: symmetric search from q0.
    colmask = [0] * n
    for r in range(n):
        m = rowmask[r]
        c = 0
        while m:
            if m & 1:
                colmask[c] |= 1 << r
            m >>= 1
            c += 1
    DC = {q0}
    frontier = [q0]
    seen_rows = set()
    while frontier:
        c = frontier.pop()
        m = colmask[c]
        r = 0
        while m:
            if (m & 1) and r not in seen_rows:
                seen_rows.add(r)
                c2 = match_row[r]
                if c2 != -1 and c2 not in DC:
                    DC.add(c2)
                    frontier.append(c2)
            m >>= 1
            r += 1

    return [(r, c) for r in sorted(DR) for c in sorted(DC)]


def completing_cells_bruteforce(rowmask, n):
    """Reference implementation used only by --selftest."""
    base = nu(rowmask, n)
    if base == n:
        return []
    out = []
    for r in range(n):
        for c in range(n):
            if rowmask[r] >> c & 1:
                continue
            rm = list(rowmask)
            rm[r] |= 1 << c
            if nu(tuple(rm), n) == n:
                out.append((r, c))
    return out


# ---------------------------------------------------------------------------
# Game state
# ---------------------------------------------------------------------------


class State:
    """Mutable position with cheap undo."""

    __slots__ = ("n", "occ", "x_rows", "o_rows", "x_moves", "o_moves", "ctx")

    def __init__(self, n):
        self.n = n
        self.occ = {}                     # cell -> 'X' | 'O'
        self.x_rows = [0] * n             # row-masks
        self.o_rows = [0] * n
        self.x_moves = []                 # cells, in order played
        self.o_moves = []
        self.ctx = {}                     # strategy context set at the tie-break

    # -- basic ops ---------------------------------------------------------
    def free(self, cell):
        return cell not in self.occ

    def play(self, cell, who):
        r, c = cell
        self.occ[cell] = who
        if who == "X":
            self.x_rows[r] |= 1 << c
            self.x_moves.append(cell)
        else:
            self.o_rows[r] |= 1 << c
            self.o_moves.append(cell)

    def unplay(self, cell, who):
        r, c = cell
        del self.occ[cell]
        if who == "X":
            self.x_rows[r] &= ~(1 << c)
            self.x_moves.pop()
        else:
            self.o_rows[r] &= ~(1 << c)
            self.o_moves.pop()

    def free_cells(self):
        n = self.n
        return [
            (r, c) for r in range(n) for c in range(n) if (r, c) not in self.occ
        ]

    # -- derived -----------------------------------------------------------
    def x_mask(self):
        return tuple(self.x_rows)

    def o_mask(self):
        return tuple(self.o_rows)

    def open_block(self):
        """H = U_R x U_C, the rows and columns free of X-stones."""
        n = self.n
        cols_used = 0
        UR = []
        for r in range(n):
            if self.x_rows[r] == 0:
                UR.append(r)
            cols_used |= self.x_rows[r]
        UC = [c for c in range(n) if not (cols_used >> c & 1)]
        return UR, UC

    def free_completions(self, who):
        mask = self.x_mask() if who == "X" else self.o_mask()
        return [f for f in completing_cells(mask, self.n) if f not in self.occ]

    def has_transversal(self, who):
        mask = self.x_mask() if who == "X" else self.o_mask()
        return nu(mask, self.n) == self.n


class VerificationError(AssertionError):
    """Raised when a claim of the proof fails at some node."""


# ---------------------------------------------------------------------------
# X's strategy (Section 4)
# ---------------------------------------------------------------------------


def phase1_candidates(st):
    """All cells X may play under the Phase-1 rule of Sec. 3 (moves 1..n-2)."""
    n = st.n
    k = len(st.x_moves) + 1
    if k == 1:
        # "Move 1: any cell."  All cells are equivalent under row/column
        # permutations, so a single representative is enough; the
        # --all-x-choices mode keeps this reduction and says so.
        return [(0, 0)]
    UR, UC = st.open_block()
    H = [(r, c) for r in UR for c in UC]
    o_last = st.o_moves[-1]
    if o_last in H:
        cand = [cell for cell in H if cell[0] == o_last[0] and st.free(cell)]
    else:
        cand = [cell for cell in H if st.free(cell)]
    if not cand:
        raise VerificationError("Phase-1 rule not executable (contradicts Lemma 4)")
    return cand


def tiebreak_candidates(st):
    """All cells X may play at move n-1 under the tie-break of Sec. 5.

    Returns a list of (cell, b, d, w).  An outcome is *admissible* if the
    cell and its opposite corner in H are both free (this is what keeps
    (b,d) free).  Preference: some outcome with 1 <= w <= n-3, else any
    with w <= n-3.
    """
    n = st.n
    UR, UC = st.open_block()
    if len(UR) != 2 or len(UC) != 2:
        raise VerificationError("open block is not 2x2 before X's move n-1")
    (u1, u2), (v1, v2) = UR, UC
    F = list(st.o_moves)  # O's n-2 early stones
    outcomes = []
    for a, ua in ((0, u1), (1, u2)):
        for c_, vc in ((0, v1), (1, v2)):
            cell = (ua, vc)
            b = u2 if a == 0 else u1
            d = v2 if c_ == 0 else v1
            if not st.free(cell) or not st.free((b, d)):
                continue  # inadmissible
            w = sum(1 for (orow, ocol) in F if orow == b or ocol == d)
            outcomes.append((cell, b, d, w))
    if not outcomes:
        raise VerificationError("no admissible tie-break cell (contradicts Sec. 5)")
    preferred = [out for out in outcomes if 1 <= out[3] <= n - 3]
    if preferred:
        return preferred
    fallback = [out for out in outcomes if out[3] <= n - 3]
    if not fallback:
        raise VerificationError("no outcome with w <= n-3 (contradicts Claim A)")
    return fallback


def build_context(st, b, d, tiebreak_cell):
    """Compute sigma, F, w, live rows, plan and the admissible (r,s) pairs."""
    n = st.n
    # sigma from X's (n-1)-matching
    sigma = {}
    for (r, c) in st.x_moves:
        sigma[r] = c
    if len(sigma) != n - 1 or b in sigma or d in sigma.values():
        raise VerificationError("X's stones are not an (n-1)-matching missing row b, col d")

    F = st.o_moves[: n - 2]
    w = sum(1 for (orow, ocol) in F if orow == b or ocol == d)

    live = [
        s for s in range(n)
        if s != b and st.free((s, d)) and st.free((b, sigma[s]))
    ]

    F_mask = [0] * n
    for (r, c) in F:
        F_mask[r] |= 1 << c
    nuF = nu(tuple(F_mask), n)

    meets_col_d = any(ocol == d for (_, ocol) in F)
    meets_row_b = any(orow == b for (orow, _) in F)

    ua = tiebreak_cell[0]

    if meets_col_d:
        plan, case = "i", "C-i"
        pairs = [(r, s) for r in live for s in live
                 if r != s and st.free((r, sigma[s]))]
    elif meets_row_b:
        plan, case = "ii", "C-ii"
        pairs = [(r, s) for r in live for s in live
                 if r != s and st.free((s, sigma[r]))]
    else:
        if nuF <= n - 3:
            plan, case = "i", "C-iii(nu<=n-3)"
            pairs = [(r, s) for r in live for s in live
                     if r != s and st.free((r, sigma[s]))]
        else:
            plan, case = "i", "C-iii(nu=n-2)"
            # rule 4.3: s := u_a, r any live row != u_a
            if ua not in live:
                raise VerificationError("u_a is not live (contradicts Claim B')")
            pairs = [(r, ua) for r in live
                     if r != ua and st.free((r, sigma[ua]))]

    if not pairs:
        raise VerificationError(f"no admissible (r,s) pair in case {case} "
                                f"(contradicts Claim B/B')")
    return dict(b=b, d=d, sigma=sigma, w=w, nuF=nuF, live=live,
                plan=plan, case=case, pairs=pairs, ua=ua)


def planned_move(ctx, which):
    """X's move at ply 2n-1 (which=1) and 2n+1 (which=2)."""
    b, d, sigma = ctx["b"], ctx["d"], ctx["sigma"]
    r, s = ctx["r"], ctx["s"]
    if ctx["plan"] == "i":
        return (b, sigma[r]) if which == 1 else (s, d)
    else:
        return (r, d) if which == 1 else (b, sigma[s])


# ---------------------------------------------------------------------------
# Exhaustive search over O's defences
# ---------------------------------------------------------------------------

def verify_worker(args):
    n, first_o_move, all_x_choices = args

    v = Verifier(
        n,
        all_x_choices=all_x_choices,
        collect_examples=True,
    )

    st = State(n)
    st.play((0, 0), "X")
    st.play(first_o_move, "O")

    v.x_node(st, 3, None)

    return v.report()


class Verifier:
    def __init__(self, n, all_x_choices=False, collect_examples=True,
                 progress_every=0):
        self.n = n
        self.all_x = all_x_choices
        self.collect = collect_examples
        self.progress_every = progress_every
        self.reset()

    def reset(self):
        n = self.n
        self.leaves = 0
        self.nodes = 0
        self.win_ply = Counter()
        self.case_count = Counter()
        self.w_count = Counter()
        self.plan_count = Counter()
        self.deviation_ply = Counter()
        self.nodes_by_ply = Counter()
        self.final_cell = Counter()
        self.block_cells = Counter()
        self.examples = {}
        self.max_win_ply = 0
        self.t0 = time.time()

    # -- recording ---------------------------------------------------------
    def record_leaf(self, st, ply, tag, deviated_at):
        self.leaves += 1
        self.win_ply[ply] += 1
        self.max_win_ply = max(self.max_win_ply, ply)
        if deviated_at:
            self.deviation_ply[deviated_at] += 1
        case = st.ctx.get("case")
        if case:
            self.case_count[case] += 1
            self.w_count[st.ctx["w"]] += 1
            self.plan_count[st.ctx["plan"]] += 1
        self.final_cell[st.x_moves[-1]] += 1
        if self.collect and case and not deviated_at:
            key = case
            if key not in self.examples:
                self.examples[key] = self.snapshot(st, ply)
        if self.progress_every and self.leaves % self.progress_every == 0:
            el = time.time() - self.t0
            print(f"    ... {self.leaves:,} lines  ({el:.1f}s)", file=sys.stderr)

    def snapshot(self, st, ply):
        n = self.n
        moves = []
        for i in range(max(len(st.x_moves), len(st.o_moves))):
            if i < len(st.x_moves):
                moves.append(("X", st.x_moves[i]))
            if i < len(st.o_moves):
                moves.append(("O", st.o_moves[i]))
        ctx = st.ctx
        return dict(
            n=n, win_ply=ply, case=ctx.get("case"), plan=ctx.get("plan"),
            w=ctx.get("w"), nuF=ctx.get("nuF"),
            b=ctx.get("b"), d=ctx.get("d"), r=ctx.get("r"), s=ctx.get("s"),
            moves=[(who, [c[0] + 1, c[1] + 1]) for who, c in moves],
        )

    # -- the search --------------------------------------------------------
    def run(self):
        st = State(self.n)
        self.x_node(st, 1, None)
        return self.report()

    def x_node(self, st, ply, deviated_at):
        """X to move at `ply` (odd)."""
        n = self.n
        self.nodes += 1
        self.nodes_by_ply[ply] += 1

        if ply > 2 * n + 3:
            raise VerificationError(f"game ran past ply 2n+3 = {2*n+3}")

        # Rule 4.4 / the win itself: if X has a free completing cell, take it.
        wins = st.free_completions("X")
        if wins:
            if self.all_x:
                for f in wins:
                    st.play(f, "X")
                    if not st.has_transversal("X"):
                        raise VerificationError("claimed winning move does not win")
                    self.record_leaf(st, ply, "win", deviated_at)
                    st.unplay(f, "X")
            else:
                f = wins[0]
                st.play(f, "X")
                if not st.has_transversal("X"):
                    raise VerificationError("claimed winning move does not win")
                self.record_leaf(st, ply, "win", deviated_at)
                st.unplay(f, "X")
            return

        if ply == 2 * n + 3:
            raise VerificationError(
                "no winning move available at ply 2n+3 (upper bound FAILS)")

        k = len(st.x_moves) + 1  # index of the X-move about to be made

        # --- Phase 1, moves 1..n-2 ---------------------------------------
        if k <= n - 2:
            cands = phase1_candidates(st)
            if not self.all_x:
                cands = cands[:1]
            for cell in cands:
                st.play(cell, "X")
                self.check_invariant_I(st)
                self.o_node(st, ply + 1, deviated_at)
                st.unplay(cell, "X")
            return

        # --- Move n-1: the tie-break of Sec. 5 ---------------------------
        if k == n - 1:
            outs = tiebreak_candidates(st)
            if not self.all_x:
                outs = outs[:1]
            for (cell, b, d, w) in outs:
                st.play(cell, "X")
                if not st.free((b, d)):
                    raise VerificationError("(b,d) not free after tie-break")
                if w > n - 3:
                    raise VerificationError("tie-break delivered w > n-3")
                ctx = build_context(st, b, d, cell)
                pairs = ctx["pairs"] if self.all_x else ctx["pairs"][:1]
                saved = st.ctx
                for (r, s) in pairs:
                    st.ctx = dict(ctx, r=r, s=s)
                    # (S): exactly one free completing cell -- a single threat
                    thr = st.free_completions("X")
                    if thr != [(b, d)]:
                        raise VerificationError(
                            f"expected the unique threat (b,d)={(b,d)}, got {thr}")
                    self.o_node(st, ply + 1, deviated_at)
                st.ctx = saved
                st.unplay(cell, "X")
            return

        # --- Phase 2: the two planned moves ------------------------------
        which = 1 if k == n else 2
        # (Ca) O must have no threat when X is about to move
        othr = st.free_completions("O")
        if othr:
            raise VerificationError(
                f"Claim C(a) fails at ply {ply}: O threatens {othr}")
        cell = planned_move(st.ctx, which)
        if not st.free(cell):
            raise VerificationError(
                f"planned move {cell} is occupied at ply {ply} (contradicts Lemma 5)")
        st.play(cell, "X")
        thr = st.free_completions("X")
        expected = 1 if which == 1 else 2
        if len(thr) != expected:
            raise VerificationError(
                f"expected {expected} free completing cell(s) at ply {ply}, "
                f"got {len(thr)}: {thr}")
        self.o_node(st, ply + 1, deviated_at)
        st.unplay(cell, "X")

    def o_node(self, st, ply, deviated_at):
        """O to move at `ply` (even).  Every legal move is tried."""
        n = self.n
        self.nodes += 1
        self.nodes_by_ply[ply] += 1

        forced = ply >= 2 * n - 2   # from ply 2n-2 on, O is under a threat
        threats = st.free_completions("X") if forced else []

        for cell in st.free_cells():
            st.play(cell, "O")
            # (Cb) / general safety: O must not complete a transversal.
            if st.has_transversal("O"):
                raise VerificationError(
                    f"Claim C(b) FAILS: O completes a transversal at ply {ply} "
                    f"with {cell}")
            if forced and cell in threats:
                self.block_cells[cell] += 1
                self.x_node(st, ply + 1, deviated_at)
            elif forced:
                # O declined to block: rule 4.4 must punish immediately.
                remaining = [f for f in threats if f != cell]
                if not remaining:
                    raise VerificationError(
                        f"rule 4.4 fails: no surviving threat after O plays {cell}")
                self.x_node(st, ply + 1, deviated_at or ply)
            else:
                self.x_node(st, ply + 1, deviated_at)
            st.unplay(cell, "O")

    def check_invariant_I(self, st):
        UR, UC = st.open_block()
        URs, UCs = set(UR), set(UC)
        for (r, c) in st.o_moves:
            if r in URs and c in UCs:
                raise VerificationError(
                    f"invariant (I) fails: O-stone {(r,c)} lies in the open block")

    # -- output ------------------------------------------------------------
    def report(self):
        n = self.n
        return dict(
            n=n,
            bound=2 * n + 3,
            verified=True,
            all_x_choices=self.all_x,
            terminal_lines=self.leaves,
            nodes_visited=self.nodes,
            max_win_ply=self.max_win_ply,
            win_ply_distribution={str(k): v for k, v in sorted(self.win_ply.items())},
            case_distribution=dict(self.case_count),
            w_distribution={str(k): v for k, v in sorted(self.w_count.items())},
            plan_distribution=dict(self.plan_count),
            deviation_ply_distribution={
                str(k): v for k, v in sorted(self.deviation_ply.items())},
            nodes_by_ply={str(k): v for k, v in sorted(self.nodes_by_ply.items())},
            elapsed_seconds=round(time.time() - self.t0, 2),
            examples=self.examples,
            final_cell_frequency={f"{r+1},{c+1}": v
                                  for (r, c), v in sorted(self.final_cell.items())},
            block_cell_frequency={f"{r+1},{c+1}": v
                                  for (r, c), v in sorted(self.block_cells.items())},
        )


# ---------------------------------------------------------------------------
# Principal variation (O blocks every time)
# ---------------------------------------------------------------------------


def principal_variation(n):
    """Play the strategy against an O who always blocks, choosing its free
    moves lexicographically.  Returns the move list and metadata."""
    st = State(n)
    ply = 1
    log = []
    while True:
        wins = st.free_completions("X")
        if wins:
            st.play(wins[0], "X")
            log.append(("X", wins[0], ply))
            return dict(moves=log, win_ply=ply, ctx=dict(st.ctx),
                        winning_set=list(st.x_moves))
        k = len(st.x_moves) + 1
        if k <= n - 2:
            cell = phase1_candidates(st)[0]
        elif k == n - 1:
            cell, b, d, w = tiebreak_candidates(st)[0]
            st.play(cell, "X")
            ctx = build_context(st, b, d, cell)
            r, s = ctx["pairs"][0]
            st.ctx = dict(ctx, r=r, s=s)
            log.append(("X", cell, ply))
            ply += 1
            cell = None
        else:
            cell = planned_move(st.ctx, 1 if k == n else 2)
        if cell is not None:
            st.play(cell, "X")
            log.append(("X", cell, ply))
            ply += 1
        # O blocks if threatened, else plays lexicographically first free cell
        thr = st.free_completions("X")
        ocell = thr[0] if thr else st.free_cells()[0]
        st.play(ocell, "O")
        log.append(("O", ocell, ply))
        ply += 1


# ---------------------------------------------------------------------------
# Self-test of the structural lemmas
# ---------------------------------------------------------------------------


def selftest(seed=12345, trials=4000):
    import random
    rng = random.Random(seed)
    print("Self-test: Lemma 1 (completing cells = D_R x D_C) against brute force")
    bad = 0
    for _ in range(trials):
        n = rng.randint(3, 7)
        cells = set()
        for _ in range(rng.randint(n - 2, min(n * n, 2 * n + 2))):
            cells.add((rng.randrange(n), rng.randrange(n)))
        rm = [0] * n
        for (r, c) in cells:
            rm[r] |= 1 << c
        rm = tuple(rm)
        fast = sorted(completing_cells(rm, n))
        slow = sorted(completing_cells_bruteforce(rm, n))
        # brute force only reports cells not already in S; Lemma 1's remark
        # says the rectangle is automatically disjoint from S, so they agree.
        if fast != slow:
            bad += 1
            print("  MISMATCH", n, sorted(cells), fast, slow)
    print(f"  {trials - bad}/{trials} random instances agree.")

    print("Self-test: Corollary 2 (a set of size < n-1 has no completing cell)")
    bad2 = 0
    for _ in range(trials):
        n = rng.randint(3, 7)
        cells = set()
        while len(cells) < n - 2:
            cells.add((rng.randrange(n), rng.randrange(n)))
        rm = [0] * n
        for (r, c) in cells:
            rm[r] |= 1 << c
        if completing_cells(tuple(rm), n):
            bad2 += 1
    print(f"  {trials - bad2}/{trials} instances have no completing cell, as claimed.")
    return bad == 0 and bad2 == 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def merge_reports(reports):
    out = reports[0].copy()

    out["terminal_lines"] = sum(
        r["terminal_lines"] for r in reports
    )

    out["nodes_visited"] = sum(
        r["nodes_visited"] for r in reports
    )

    out["max_win_ply"] = max(
        r["max_win_ply"] for r in reports
    )

    out["elapsed_seconds"] = round(
        sum(r["elapsed_seconds"] for r in reports), 2
    )

    for key in [
        "win_ply_distribution",
        "case_distribution",
        "w_distribution",
        "plan_distribution",
        "deviation_ply_distribution",
        "nodes_by_ply",
        "final_cell_frequency",
        "block_cell_frequency",
    ]:
        c = Counter()
        for r in reports:
            c.update(r[key])
        out[key] = dict(c)

    out["examples"] = {}
    for r in reports:
        out["examples"].update(r["examples"])

    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=4, help="board size (default 4)")
    ap.add_argument("--outdir", default="results", help="output directory")
    ap.add_argument("--all-x-choices", action="store_true",
                    help="branch over every choice the Sec. 4 strategy leaves "
                         "open (verifies the strategy CLASS, not one "
                         "instantiation); X's first move is fixed to (1,1) by "
                         "the row/column symmetry of the empty board")
    ap.add_argument("--selftest", action="store_true",
                    help="cross-check Lemma 1 and Corollary 2 against brute force")
    ap.add_argument("--no-figures", action="store_true")
    ap.add_argument("--progress", type=int, default=0,
                    help="print progress every N terminal lines")
    args = ap.parse_args(argv)

    if args.selftest:
        ok = selftest()
        return 0 if ok else 1

    n = args.n
    sys.setrecursionlimit(10000)
    os.makedirs(args.outdir, exist_ok=True)

    print(f"Verifying the upper bound  ply <= 2n+3 = {2*n+3}  for n = {n}")
    print(f"  mode: {'all admissible X choices' if args.all_x_choices else 'one fixed instantiation'}")
    jobs = [
        (n, (r, c), args.all_x_choices)
        for r in range(n)
        for c in range(n)
        if (r, c) != (0, 0)
    ]

    try:
        with Pool(processes=cpu_count()) as pool:
            reports = pool.map(verify_worker, jobs)

        rep = merge_reports(reports)

    except VerificationError as e:
        print(f"\n  *** VERIFICATION FAILED: {e}", file=sys.stderr)
        return 2

    pv = principal_variation(n)
    rep["principal_variation"] = dict(
        win_ply=pv["win_ply"],
        moves=[(who, [c[0] + 1, c[1] + 1], p) for who, c, p in pv["moves"]],
        case=pv["ctx"].get("case"), plan=pv["ctx"].get("plan"),
    )

    print(f"  terminal lines : {rep['terminal_lines']:,}")
    print(f"  nodes visited  : {rep['nodes_visited']:,}")
    print(f"  max win ply    : {rep['max_win_ply']}  (bound {2*n+3})")
    print(f"  cases hit      : {rep['case_distribution']}")
    print(f"  elapsed        : {rep['elapsed_seconds']}s")

    path = os.path.join(args.outdir, f"report_n{n}.json")
    with open(path, "w") as fh:
        json.dump(rep, fh, indent=2, default=str)
    print(f"  wrote {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())