# Brute-force checks

Python scripts used while the statements of Part B were being fixed. They are not part of
the paper's evidence (every claim in the paper is proved in Lean); they are kept so that the
search that produced the examples can be repeated.

* `gas.py`: random guarded action systems with three condition sets; blocking semantics.
* `checkA.py`, `checkA2.py`: state-level and configuration-level versions of claim A.
* `checkB.py`, `checkB4.py`: event transparency, homogeneous step conservativity,
  Janicki-soundness, reachability, on three and four actions.
* `checkC.py`: representability of histories by precedence and weak precedence.
* `nets.py`, `runnets.py`: the same on net-like systems (places, arcs, contexts).
* `cexA.py`: the three-action system that is pairwise sound at the state level but not sound.
* `brute.py`, `charac.py`, `marker.py`, `jsound.py`: the Part A checks.
* `table_*.txt`: the tables reported in the research notes.

Run with Python 3 from this folder, no dependencies: `python3 checkB.py 3 400 7 committed overall`
(arguments: number of actions, number of random systems, seed, discipline, condition placement).
Each script prints its tables and writes a pickle of the systems it found next to the script;
set the environment variable `CHECK_OUT` to write them elsewhere. `showwit.py <pickle>` prints
the witnesses in a pickle.
