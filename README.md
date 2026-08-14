# The transversal achievement game on a square grid

Supplementary material for **"The transversal achievement game on a square grid"** — [arXiv:2608.13501](http://arxiv.org/abs/2608.13501). This repository contains everything used to produce the computational and formal results in the paper:

* an exhaustive game-tree verifier that plays the strategy of §4 against every legal defense by O, for $n = 4, 5, 6$, checking every structural invariant the proof asserts;
* the machine-generated verification reports those runs produced (the source of Table 1 and Appendix B);
* a Lean 4 formalization of Theorem A and the supporting lemmas (Appendix C);
* the figure-generation scripts for the diagrams in the paper and the worked $6 \times 6$ playthrough (Appendix D).

## Layout

```
transversal_verify.py       Exhaustive verification of the claims of the paper
transversal_examples.py     Regenerates the figures and worked examples in examples/
transversal_playthrough.py  Regenerates the 6x6 playthrough panels in playthrough_6x6/
transversal_play.py         Interactive click-to-play board, for exploring the game by hand

results/                    Verification reports
  report_n4.json
  report_n5.json
  report_n6.json

examples/                   Generated figures + move-history CSVs used in the paper
playthrough_6x6/            Generated per-ply panels of the Appendix D playthrough

lean_verification/          Lean 4 formalization (see below)
```

`examples/` and `playthrough_6x6/` hold generated PNG and CSV output; both directories are reproduced from scratch by running their respective scripts.

## Requirements

The Python scripts target Python 3.9+ and use only the standard library plus `matplotlib` (needed for the three figure/interaction scripts; `transversal_verify.py` needs nothing beyond the standard library).

```bash
pip install matplotlib
```

The Lean development requires [`elan`](https://github.com/leanprover/elan); the toolchain and Mathlib revision are pinned in `lean_verification/`.

## Lean 4 formalization

`lean_verification/` is a standalone Lake project pinned to Lean `v4.28.0` and the matching Mathlib revision (see `lean-toolchain` and `lake-manifest.json`). The formalization was produced with the assistance of Aristotle and checked by the Lean kernel.

```bash
cd lean_verification
lake exe cache get     # fetch prebuilt Mathlib oleans
lake build
```

The headline statements are in `project/Main.lean`, in the `Transversal` namespace:

* `theoremA` — X wins the $1 \times 1$ game with their first stone; for every $n \ge 4$, X wins with their $(n+2)$-nd stone, i.e. by ply $2n+3$; and neither player can force a win on the $2 \times 2$ board.
* `three_is_a_draw` — neither player can force a win on the $3 \times 3$ board, settled by a kernel-checked exhaustive search rather than quoted from the literature.
* `player_two_never_wins` — the strategy-stealing remark of §2, for every $n$.

The development is organized to track the paper:

| Module | Content |
| --- | --- |
| `Basic.lean` | Cells, matchings, $\nu$, transversals, completing cells, $D_R$/$D_C$; inequalities (5.1) and (5.2) |
| `Threat.lean` | Lemma 1 (threat structure) and Corollary 2 (tempo) — via a Hall-type argument in place of the paper's alternating path |
| `Rectangle.lean` | Lemma 3 (growth of the threat rectangle), cases (a)–(d), and the following remark |
| `Game.lean` | Positions, `XCanWin` / `OCanWin` by backward induction |
| `Stealing.lean` | Strategy stealing: Player 2 never wins |
| `Phase1.lean` | The open-block invariant, the tie-break, and Lemma 8 (structure of $F$ when $w = 0$) |
| `Pairs.lean` | Live rows, inequality (4.1), Lemmas 9–11 |
| `NoDeviation.lean` | Lemma 12 (no defensive deviation) |
| `Phase2.lean` | Plans (i) and (ii): X wins with three more stones |
| `TheoremA.lean` | Assembly of the $n \ge 4$ case |
| `SmallCases.lean` | $n = 1$ and $n = 2$ |
| `Convert.lean`, `ThreeByThree.lean` | Decidable transversal test on the $3 \times 3$ board and the certified backward-induction search |
| `Main.lean` | `theoremA`, `three_is_a_draw` |

## Citation

```bibtex
@misc{guan2026transversal,
  title  = {The transversal achievement game on a square grid},
  author = {Guan, Kevin},
  year   = {2026},
  eprint = {2608.13501},
  archivePrefix = {arXiv},
  primaryClass  = {math.CO}
}
```

MSC: 91A05, 05C57, 91A43, 91A46.

## License

The paper is released under CC BY-ND 4.0. The verification and figure code is placed in the public domain (CC0).