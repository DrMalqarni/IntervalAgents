# IntervalAgents

Lean 4 companion to the paper *Actions Take Time: Transparency Conditions for the Interval
Semantics of Guarded Actions*.

The development formalises guarded action systems with durative actions (conditions read at
the start, over all, and at the end of an action; effects split into an acquire part and a
release part), their interval semantics from coherent configurations, homogeneous event steps,
and proves the paper's theorems: the characterisation of step conservativity by acquire
transparency (Part A), the characterisation of homogeneous step conservativity by event
transparency and of Janicki-soundness by the swap conditions (Part B), the lock theorem, the
temporal-gap theorem, and all the finite examples of the paper by complete enumeration,
including the swap classes (histories) of Section 7.

## Build

Requires [elan](https://github.com/leanprover/elan). From this folder:

```
lake exe cache get   # downloads prebuilt Mathlib
lake build
```

Toolchain: `leanprover/lean4:v4.36.0-rc2`, Mathlib `v4.36.0-rc2`. A full build after the cache
download takes a few minutes; the examples are checked by `decide` in the kernel. The
development is about 3,000 lines.

## Files

| File | Contents |
| --- | --- |
| `IntervalAgents/Basic.lean` | Part A: the `GAS` structure (at-start conditions, acquire and release parts, conflict), step semantics, interval semantics from states, acquire-transparency, step-conservativity. |
| `IntervalAgents/Characterization.lean` | Theorem 4.3: `GAS.transparent_iff_conservative`. |
| `IntervalAgents/Exec.lean` | Computable interval semantics for `GAS`, complete enumeration of runnable words, the committed corollary. |
| `IntervalAgents/Examples.lean` | The review and release net (Example 4.14) under three disciplines; the strict-expressiveness witness. |
| `IntervalAgents/Durative/Basic.lean` | Part B: the `DAS` structure (start, over-all and end conditions), configurations with `Finset` in-flight sets, coherence, event enabledness, runs, homogeneous steps, `HSC`, event transparency `ET_BB`/`ET_EE` with their halves, swap conditions `J_BB`/`J_EE`, `JSound`. |
| `IntervalAgents/Durative/Characterization.lean` | Theorem 5.4 (`hsc_fwd_iff`, `hsc_bwd_iff`, `hsc_iff_et`), Theorem 5.5 (`jsound_iff`, `hsc_imp_jsound`), and the lemmas `not_hsc_of_not_ET_BB`, `not_hsc_of_not_ET_EE`, `not_jsound_of_not_J_BB`, `not_jsound_of_not_J_EE` used by the counterexamples. |
| `IntervalAgents/Durative/Bridge.lean` | Proposition 5.6: the embedding of `GAS` into `DAS`; Theorem 4.7 (`toDAS_jsound_iff`); Corollary 4.10 (`repair_conservative`, `repair_least`); Corollary 4.11 (`swapRepair_jsound`, `swapRepair_least`). |
| `IntervalAgents/Durative/Lock.lean` | Theorem 5.7 (`committed_ET_BB`), Theorem 5.9 (`lock_hsc`, `two_inflight_iff`, `repair_hsc`). |
| `IntervalAgents/Durative/Reach.lean` | Theorem 6.3 (`intReach_iff_seqReach`) and the invariant principle `seqReach_inv`. |
| `IntervalAgents/Durative/Exec.lean` | Decidability instances, computable runs (`runB`, `runs_iff_runB`), complete words with a proved completeness theorem (`mem_completeWords_iff`), precedence matrices, end-point histories (`history`, `mem_history_iff`), invariant structures, `representable`, `closed`, swap classes by breadth-first closure (`swaps`, `swapBFS`, `swapClass`). |
| `IntervalAgents/Durative/Examples.lean` | Theorem 5.11 (the two sound cells and the seven counterexamples, each failing both conservativity and soundness), Proposition 6.4 and Corollary 6.5 (required-concurrency witnesses), Propositions 7.3 and 7.4 and Remark 7.5 (non-representable histories), Example 4.8 (sound but not transparent). |
| `IntervalAgents/Durative/Histories.lean` | Swap classes: Propositions 7.3 and 7.4 and Remark 7.5 are single classes (15, 45 and 81 runs); Example 7.2, the review and release net under the committed discipline (10 runs, end-point history not representable, two swap classes of 1 and 9 runs, both representable); Remark 5.10, the three-action system with three incomparable repairs. |
| `checks/` | Python scripts used to search for the examples (not part of the proofs). |

## Statements of the paper and their Lean names

| Paper | Lean | How |
| --- | --- | --- |
| Theorem 4.3 (characterisation, at start) | `GAS.transparent_iff_conservative` | general |
| Theorem 4.7 (soundness, at start) | `GAS.toDAS_jsound_iff`, `GAS.transparent_swapCond` | general |
| Example 4.8 (sound, not transparent) | `SoundNotTransparent.swapCond`, `SoundNotTransparent.not_transparent`, `SoundNotTransparent.jsound` | decide |
| Corollary 4.10 (least conflict extension, conservativity) | `GAS.repair_conservative`, `GAS.repair_least` | general |
| Corollary 4.11 (least conflict extension, soundness) | `GAS.swapRepair_swapCond`, `GAS.swapRepair_jsound`, `GAS.swapRepair_least` | general |
| Corollary 4.12 (committed) | `GAS.committed_conservative`, `DAS.committed_atStart_hsc` | general |
| Example 4.14 (review and release) | `Fig1.committed_runs_eq_thesis`, `Fig1.doubleArc_runs_eq_thesis`, `Fig1.consuming_runs`, `Fig1.consuming_not_transparent` | enumeration + decide |
| Theorem 5.4 (characterisation, Part B) | `DAS.hsc_fwd_iff`, `DAS.hsc_bwd_iff`, `DAS.hsc_iff_et` | general |
| Theorem 5.5 (soundness, Part B) | `DAS.jsound_iff`, `DAS.hsc_imp_jsound` | general |
| Proposition 5.6 (at-start systems) | `GAS.toDAS_ET_BB_iff`, `GAS.toDAS_ET_EE`, `GAS.toDAS_hsc_iff_conservative`, `GAS.toDAS_jsound_iff` | general |
| Theorem 5.7 (committed beginnings) | `DAS.committed_ET_BB` | general |
| Theorem 5.9 (lock) | `DAS.lock_hsc`, `DAS.two_inflight_iff`, `DAS.repair_hsc` | general |
| Remark 5.10 (no least repair in Part B) | `Three.nlr0_not_hsc`, `Three.nlrAB_hsc`, `Three.nlrAC_hsc`, `Three.nlrBC_hsc` | decide |
| Theorem 5.11 (i), (ii) | `DAS.committed_atStart_hsc`, `DAS.startOnly_atEnd_hsc` | general |
| Theorem 5.11 (iii) | `Two.committedOverall_not_hsc`, `Two.committedOverall_not_jsound`, and the same pair for `committedAtEnd`, `startOnlyAtStart`, `startOnlyOverall`, `consumingAtStart`, `consumingOverall`, `consumingAtEnd` | decide |
| Theorem 6.3 (no gap, no required concurrency) | `DAS.intReach_iff_seqReach` | general |
| Proposition 6.4, Corollary 6.5 (witnesses) | `Two.gapStartEnd_int/_notSeq`, `Two.gapEndStart_int/_notSeq`, `Two.gapBothEnds_int/_notSeq`, `Two.gapBothEndsOverall_int/_notSeq`, `Two.gapBothEndsAtEnd_int/_notSeq` | decide + invariant |
| Example 7.2 (review and release: end points are not enough) | `Three.fig1_history_size`, `Three.fig1_not_representable`, `Three.fig1_two_classes` | decide |
| Proposition 7.3 (beginning against beginning) | `Three.beginBegin_history_size`, `Three.beginBegin_single_class`, `Three.beginBegin_not_representable` | decide |
| Proposition 7.4 (ending against ending) | `Three.endEnd_history_size`, `Three.endEnd_single_class`, `Three.endEnd_not_representable`; the two-action history: `Two.endEndAB_history_size`, `Two.endEndAB_representable`, `Two.endEndAB_not_closed` | decide |
| Remark 7.5 (disjunctive condition) | `Three.disjunctive_history_size`, `Three.disjunctive_single_class`, `Three.disjunctive_not_representable`, `Three.disjunctive_hsc` | decide, general |

Statements about the concrete systems quantify over all configurations, all words of a given
length, or all complete words over the actions, never over a chosen list: `GAS.explore` and
`DAS.completeWords` are enumerations whose completeness is proved (`GAS.mem_explore`,
`DAS.mem_completeWords_iff`), `DAS.history` is characterised by `DAS.mem_history_iff` as the
set of complete words that run between the two configurations, and `DAS.swapClass` is the
closure of one run under adjacent swaps inside the end-point history, so a statement that a
class has a given size and covers the history is a statement about the whole history.

## Checking that the definitions say what the paper says

The kernel checks proofs, not the adequacy of definitions. The correspondence to read is:
`DAS` (Definition 3.1), `DAS.Coherent`, `DAS.enB`, `DAS.enE`, `DAS.Runs` (Definition 3.2),
`DAS.BStep`, `DAS.EStep`, `DAS.HSC` (Definition 5.2), `DAS.ET_BB`, `DAS.ET_EE` (Definition 5.3),
`DAS.JSound` (Definition 4.5, read through `GAS.toDAS` for Part A), `GAS.Conservative`
(Definition 4.1), `GAS.Transparent` (Definition 4.2), `GAS.SwapCond` (Definition 4.6),
`GAS.Opaque` and `GAS.SwapViolating` (Corollaries 4.10 and 4.11), `DAS.Lock` and
`DAS.Interferes` (Definition 5.8 and Theorem 5.9), `DAS.NoGap`, `DAS.SeqReach`, `DAS.IntReach`
(Section 6), and `DAS.history`, `DAS.extendsInv`, `DAS.representable`, `DAS.closed`,
`DAS.swapClass` (Definition 7.1). Two conventions differ harmlessly from the paper: the Lean
structures do not assume the set of actions finite (the theorems are more general), and
`DAS.HSC` quantifies over all duplicate-free lists rather than over pairwise independent sets,
which makes no difference because no order of a non-independent set runs.

## Trust

No `sorry`, `admit` or `native_decide`. `#print axioms` reports at most `propext`,
`Quot.sound` and `Classical.choice` for every theorem listed above.

## Not mechanised

* Proposition 8.1 (the double-arc system of an inhibitor net is its committed discipline), a
  statement about nets, checked on the net of Example 4.14 only.
* Corollary 4.4 (block runs), proved on paper by induction from Theorem 4.3.
* Fishburn's representation theorem and the fact that complete words with the same interval
  order differ by swaps of adjacent events of the same kind.

## Paper

The folder `paper/` holds the LaTeX source and a PDF of the submitted version of the paper. The
manuscript is a preprint for reading and is not covered by the repository licence (see
`paper/README.md`); the published version will be the version of record.

## Licence and citation

Apache License 2.0 (see `LICENSE`). To cite, use `CITATION.cff`. Release v1.0.0 is archived at
Zenodo under DOI [10.5281/zenodo.23909483](https://doi.org/10.5281/zenodo.23909483) (all versions:
[10.5281/zenodo.23909482](https://doi.org/10.5281/zenodo.23909482)).
