import IntervalAgents.Exec

/-!
# The concrete results of the paper

* `Fig1`: the review and release net (Fig. 1 of the paper, Fig. 5.1 of the 2016 thesis)
  under three disciplines: committed, consuming (dirty-read), and double-arc (in-flight markers).
  - `consuming_not_transparent`: Corollary 3 (consuming is not transparent).
  - `consuming_bad_run`, `step_bc_not_enabled`: the witness run and the failing step.
  - `committed_runs_eq_thesis`, `doubleArc_runs_eq_thesis`, `consuming_runs`: Proposition 2.
  - `doubleArc_transparent`: Proposition 1 on this net.
* `Strict`: the witness of Theorem 3 (strict expressiveness).

All facts about these finite systems are checked by `decide`, so they rest on the kernel only.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace IntervalAgents

open GAS

/-! ## The review and release net -/

namespace Fig1

/-- Transitions: `a` submit, `b` review, `c` release. -/
inductive T | a | b | c
  deriving DecidableEq, Repr

/-- Markings, with in-flight markers `ma mb mc` used only by the double-arc discipline. -/
structure M where
  s1 : Bool
  s2 : Bool
  s3 : Bool
  s4 : Bool
  s5 : Bool
  ma : Bool
  mb : Bool
  mc : Bool
  deriving DecidableEq, Repr

/-- Preconditions: input place marked, output place empty (contact-freeness). -/
def preB : T → M → Bool
  | .a, m => m.s1 && !m.s3
  | .b, m => m.s3 && !m.s5
  | .c, m => m.s2 && !m.s4

/-- Guards of the original net: `s3` inhibits `c`. -/
def grdB : T → M → Bool
  | .c, m => !m.s3
  | _, _ => true

/-- Guards of the double-arc discipline: `c` is also inhibited while `b`, which consumes from
`s3`, is in flight. -/
def grdDA : T → M → Bool
  | .c, m => !m.s3 && !m.mb
  | _, _ => true

/-- `a` and `b` share the place `s3`. -/
def confB : T → T → Bool
  | .a, .b => true
  | .b, .a => true
  | _, _ => false

/-- The effect of each transition. -/
def effM : T → M → M
  | .a, m => { m with s1 := false, s3 := true }
  | .b, m => { m with s3 := false, s5 := true }
  | .c, m => { m with s2 := false, s4 := true }

/-- Consuming: remove the input place at the beginning. -/
def acqCons : T → M → M
  | .a, m => { m with s1 := false }
  | .b, m => { m with s3 := false }
  | .c, m => { m with s2 := false }

/-- Consuming: add the output place at the end. -/
def relCons : T → M → M
  | .a, m => { m with s3 := true }
  | .b, m => { m with s5 := true }
  | .c, m => { m with s4 := true }

/-- Double arc: remove the input place and set the marker at the beginning. -/
def acqDA : T → M → M
  | .a, m => { m with s1 := false, ma := true }
  | .b, m => { m with s3 := false, mb := true }
  | .c, m => { m with s2 := false, mc := true }

/-- Double arc: clear the marker and add the output place at the end. -/
def relDA : T → M → M
  | .a, m => { m with ma := false, s3 := true }
  | .b, m => { m with mb := false, s5 := true }
  | .c, m => { m with mc := false, s4 := true }

/-- The committed discipline. -/
def committed : GAS M T where
  pre t m := preB t m = true
  grd t m := grdB t m = true
  acq _ m := m
  rel := effM
  conflict t u := confB t u = true
  conflict_symm := by intro a b; cases a <;> cases b <;> simp [confB]
  acq_acq := by intros; rfl
  rel_rel := by
    intro a b hab hc s; cases a <;> cases b <;> cases s <;> simp_all [effM, confB]
  acq_rel := by intros; rfl

/-- The consuming (dirty-read) discipline: the naive translation of the 2016 thesis. -/
def consuming : GAS M T where
  pre t m := preB t m = true
  grd t m := grdB t m = true
  acq := acqCons
  rel := relCons
  conflict t u := confB t u = true
  conflict_symm := by intro a b; cases a <;> cases b <;> simp [confB]
  acq_acq := by
    intro a b hab hc s; cases a <;> cases b <;> cases s <;> simp_all [acqCons, confB]
  rel_rel := by
    intro a b hab hc s; cases a <;> cases b <;> cases s <;> simp_all [relCons, confB]
  acq_rel := by
    intro a b hab hc s; cases a <;> cases b <;> cases s <;> simp_all [acqCons, relCons, confB]

/-- The double-arc discipline: the interval representation of the 2015 paper. -/
def doubleArc : GAS M T where
  pre t m := preB t m = true
  grd t m := grdDA t m = true
  acq := acqDA
  rel := relDA
  conflict t u := confB t u = true
  conflict_symm := by intro a b; cases a <;> cases b <;> simp [confB]
  acq_acq := by
    intro a b hab hc s; cases a <;> cases b <;> cases s <;> simp_all [acqDA, confB]
  rel_rel := by
    intro a b hab hc s; cases a <;> cases b <;> cases s <;> simp_all [relDA, confB]
  acq_rel := by
    intro a b hab hc s; cases a <;> cases b <;> cases s <;> simp_all [acqDA, relDA, confB]

instance (t : T) (m : M) : Decidable (committed.en t m) :=
  inferInstanceAs (Decidable (preB t m = true ∧ grdB t m = true))
instance (t : T) (m : M) : Decidable (consuming.en t m) :=
  inferInstanceAs (Decidable (preB t m = true ∧ grdB t m = true))
instance (t : T) (m : M) : Decidable (doubleArc.en t m) :=
  inferInstanceAs (Decidable (preB t m = true ∧ grdDA t m = true))
instance (t u : T) : Decidable (committed.conflict t u) :=
  inferInstanceAs (Decidable (confB t u = true))
instance (t u : T) : Decidable (consuming.conflict t u) :=
  inferInstanceAs (Decidable (confB t u = true))
instance (t u : T) : Decidable (doubleArc.conflict t u) :=
  inferInstanceAs (Decidable (confB t u = true))

/-- Initial marking `{s1, s2}`. -/
def m0 : M := ⟨true, true, false, false, false, false, false, false⟩
/-- Final marking `{s4, s5}`. -/
def mF : M := ⟨false, false, false, true, true, false, false, false⟩
/-- The marking `{s2, s3}` reached after `a`. -/
def m23 : M := ⟨false, true, true, false, false, false, false, false⟩

open Ev

/-- All six events. -/
def evs : List (Ev T) := [B .a, E .a, B .b, E .b, B .c, E .c]

theorem mem_evs : ∀ e, e ∈ evs := by
  intro e; cases e with
  | B t => cases t <;> simp [evs]
  | E t => cases t <;> simp [evs]

/-- The ten interval firing sequences of the 2016 thesis (Ch. 5). -/
def thesisRuns : List (List (Ev T)) :=
  [ [B .a, E .a, B .b, E .b, B .c, E .c], [B .c, E .c, B .a, E .a, B .b, E .b],
    [B .a, B .c, E .c, E .a, B .b, E .b], [B .a, B .c, E .a, E .c, B .b, E .b],
    [B .c, B .a, E .c, E .a, B .b, E .b], [B .c, B .a, E .a, E .c, B .b, E .b],
    [B .a, B .c, E .a, B .b, E .b, E .c], [B .a, B .c, E .a, B .b, E .c, E .b],
    [B .c, B .a, E .a, B .b, E .b, E .c], [B .c, B .a, E .a, B .b, E .c, E .b] ]

/-- The two extra runs of the consuming discipline, where review and release overlap. -/
def extraRuns : List (List (Ev T)) :=
  [ [B .a, E .a, B .b, B .c, E .c, E .b], [B .a, E .a, B .b, B .c, E .b, E .c] ]

/-- **Corollary 3.** The consuming discipline is not acquire-transparent: beginning the
review `b` in `{s2, s3}` enables the release `c`. -/
theorem consuming_not_transparent : ¬ consuming.Transparent := by
  intro h
  have hi : consuming.Indep .b .c := ⟨by decide, by decide⟩
  have := h .b .c hi m23 (by decide)
  revert this
  decide

/-- Hence, by the characterisation, the consuming discipline is not step-conservative. -/
theorem consuming_not_conservative : ¬ consuming.Conservative :=
  fun h => consuming_not_transparent ((consuming.transparent_iff_conservative).2 h)

/-- The witness run of Corollary 3 under the consuming discipline. -/
theorem consuming_bad_run :
    consuming.Runs (m0, []) [B .a, E .a, B .b, B .c, E .c, E .b] (mF, []) := by
  rw [runs_iff_runB]; decide

/-- The step `{b, c}` is not enabled after `a`. -/
theorem step_bc_not_enabled : ∀ m', ¬ consuming.StepFires [.b, .c] m23 m' := by
  rintro m' ⟨-, hen, -⟩
  have := hen .c (by simp)
  revert this; decide

/-- The same word is not a committed run. -/
theorem committed_no_bad_run :
    ∀ c, ¬ committed.Runs (m0, []) [B .a, E .a, B .b, B .c, E .c, E .b] c := by
  intro c h
  rw [runs_iff_runB] at h
  have hn : committed.runB (m0, []) [B .a, E .a, B .b, B .c, E .c, E .b] = none := by decide
  rw [hn] at h; cases h

/-- **Proposition 1 (on this net).** The double-arc discipline is acquire-transparent. -/
theorem doubleArc_transparent : doubleArc.Transparent := by
  intro a b hab m _
  obtain ⟨hne, hc⟩ := hab
  cases a <;> cases b <;> simp_all [GAS.en, doubleArc, preB, grdDA, acqDA, confB]

/-- **Proposition 2.** Committed: the complete runs of length six from `{s1, s2}` to
`{s4, s5}` are exactly the ten runs of the thesis. -/
theorem committed_runs_eq_thesis :
    ∀ w, w.length = 6 → (committed.Runs (m0, []) w (mF, []) ↔ w ∈ thesisRuns) := by
  intro w hw
  rw [runs_iff_runB]
  constructor
  · intro h
    have hm := committed.mem_explore evs mem_evs w _ _ h
    rw [hw] at hm
    have key : ∀ p ∈ committed.explore evs (m0, []) 6, p.2 = (mF, []) → p.1 ∈ thesisRuns := by
      decide
    exact key (w, (mF, [])) hm rfl
  · intro hmem
    have key : ∀ v ∈ thesisRuns, committed.runB (m0, []) v = some (mF, []) := by decide
    exact key w hmem

/-- **Proposition 2.** Double arc: the same ten runs. -/
theorem doubleArc_runs_eq_thesis :
    ∀ w, w.length = 6 → (doubleArc.Runs (m0, []) w (mF, []) ↔ w ∈ thesisRuns) := by
  intro w hw
  rw [runs_iff_runB]
  constructor
  · intro h
    have hm := doubleArc.mem_explore evs mem_evs w _ _ h
    rw [hw] at hm
    have key : ∀ p ∈ doubleArc.explore evs (m0, []) 6, p.2 = (mF, []) → p.1 ∈ thesisRuns := by
      decide
    exact key (w, (mF, [])) hm rfl
  · intro hmem
    have key : ∀ v ∈ thesisRuns, doubleArc.runB (m0, []) v = some (mF, []) := by decide
    exact key w hmem

/-- **Proposition 2.** Consuming: the ten runs of the thesis and exactly two more. -/
theorem consuming_runs :
    ∀ w, w.length = 6 →
      (consuming.Runs (m0, []) w (mF, []) ↔ w ∈ thesisRuns ∨ w ∈ extraRuns) := by
  intro w hw
  rw [runs_iff_runB]
  constructor
  · intro h
    have hm := consuming.mem_explore evs mem_evs w _ _ h
    rw [hw] at hm
    have key : ∀ p ∈ consuming.explore evs (m0, []) 6, p.2 = (mF, []) →
        p.1 ∈ thesisRuns ∨ p.1 ∈ extraRuns := by
      decide
    exact key (w, (mF, [])) hm rfl
  · intro hmem
    have key : ∀ v ∈ thesisRuns ++ extraRuns, consuming.runB (m0, []) v = some (mF, []) := by
      decide
    exact key w (List.mem_append.2 hmem)

end Fig1

/-! ## Strict expressiveness -/

namespace Strict

inductive T | a | b | c
  deriving DecidableEq, Repr

/-- `da`, `db`, `dc` record completion of `a`, `b`, `c`. -/
structure St where
  da : Bool
  db : Bool
  dc : Bool
  deriving DecidableEq, Repr

def preB : T → St → Bool
  | .a, s => !s.da
  | .b, s => !s.db && s.da
  | .c, s => !s.dc

def grdB : T → St → Bool
  | .a, s => !s.dc
  | .b, s => !s.dc
  | .c, s => !s.da

def effS : T → St → St
  | .a, s => { s with da := true }
  | .b, s => { s with db := true }
  | .c, s => { s with dc := true }

/-- The witness system, under the committed discipline, with no conflicts. -/
def G : GAS St T where
  pre t s := preB t s = true
  grd t s := grdB t s = true
  acq _ s := s
  rel := effS
  conflict _ _ := False
  conflict_symm := fun _ _ h => h
  acq_acq := by intros; rfl
  rel_rel := by
    intro a b hab _ s; cases a <;> cases b <;> cases s <;> simp_all [effS]
  acq_rel := by intros; rfl

instance (t : T) (s : St) : Decidable (G.en t s) :=
  inferInstanceAs (Decidable (preB t s = true ∧ grdB t s = true))
instance (t u : T) : Decidable (G.conflict t u) := inferInstanceAs (Decidable False)

def s0 : St := ⟨false, false, false⟩
def sStar : St := ⟨true, true, true⟩

open Ev

/-- A complete committed run reaches `sStar`. -/
theorem run_reaches :
    G.Runs (s0, []) [B .a, B .c, E .a, B .b, E .c, E .b] (sStar, []) := by
  rw [runs_iff_runB]; decide

def evsS : List (Ev T) := [B T.a, E T.a, B T.b, E T.b, B T.c, E T.c]

theorem mem_evsS : ∀ e, e ∈ evsS := by
  intro e; cases e with
  | B t => cases t <;> simp [evsS]
  | E t => cases t <;> simp [evsS]

/-- The complete runs of length six reaching `sStar`: exactly these four words. -/
def fourRuns : List (List (Ev T)) :=
  [ [B T.a, B T.c, E T.a, B T.b, E T.b, E T.c], [B T.a, B T.c, E T.a, B T.b, E T.c, E T.b],
    [B T.c, B T.a, E T.a, B T.b, E T.b, E T.c], [B T.c, B T.a, E T.a, B T.b, E T.c, E T.b] ]

theorem runs_to_sStar :
    ∀ w, w.length = 6 → (G.Runs (s0, []) w (sStar, []) ↔ w ∈ fourRuns) := by
  intro w hw
  rw [runs_iff_runB]
  constructor
  · intro h
    have hm := G.mem_explore evsS mem_evsS w _ _ h
    rw [hw] at hm
    have key : ∀ p ∈ G.explore evsS (s0, []) 6, p.2 = (sStar, []) → p.1 ∈ fourRuns := by
      decide
    exact key (w, (sStar, [])) hm rfl
  · intro hmem
    have key : ∀ v ∈ fourRuns, G.runB (s0, []) v = some (sStar, []) := by decide
    exact key w hmem

/-- The effect of a list of actions sets the corresponding flags. -/
theorem effL_eq : ∀ (U : List T) (s : St),
    G.effL U s = ⟨s.da || decide (T.a ∈ U), s.db || decide (T.b ∈ U), s.dc || decide (T.c ∈ U)⟩ := by
  intro U
  induction U with
  | nil => intro s; simp [GAS.effL]
  | cons x r ih =>
    intro s
    have e : G.effL (x :: r) s = G.effL r (G.eff x s) := rfl
    rw [e, ih]
    cases x <;> cases s <;> simp [GAS.eff, G, effS]

/-- The invariant: `db` implies `da`, and `db` and `dc` never hold together. -/
def Inv (s : St) : Prop := (s.db = true → s.da = true) ∧ ¬ (s.db = true ∧ s.dc = true)

instance (s : St) : Decidable (Inv s) := by unfold Inv; infer_instance

theorem inv_step_core : ∀ (s : St) (x y z : Bool), Inv s →
    (x = true → preB .a s = true ∧ grdB .a s = true) →
    (y = true → preB .b s = true ∧ grdB .b s = true) →
    (z = true → preB .c s = true ∧ grdB .c s = true) →
    Inv ⟨s.da || x, s.db || y, s.dc || z⟩ := by
  rintro ⟨da, db, dc⟩ x y z
  cases da <;> cases db <;> cases dc <;> cases x <;> cases y <;> cases z <;>
    simp [Inv, preB, grdB]

theorem inv_step {U : List T} {s s' : St} (hs : Inv s) (h : G.StepFires U s s') : Inv s' := by
  obtain ⟨-, hen, rfl⟩ := h
  rw [effL_eq]
  exact inv_step_core s _ _ _ hs (fun hx => hen _ (by simpa using hx))
    (fun hy => hen _ (by simpa using hy)) (fun hz => hen _ (by simpa using hz))

theorem inv_reach {s s' : St} (h : G.StepReach s s') (hs : Inv s) : Inv s' := by
  induction h with
  | refl => exact hs
  | step U hf _ ih => exact ih (inv_step hs hf)

/-- **Theorem 3.** No step sequence leads from `s0` to `sStar`. -/
theorem no_step_sequence : ¬ G.StepReach s0 sStar := by
  intro h
  have := inv_reach h (by decide)
  revert this; decide

end Strict

end IntervalAgents
