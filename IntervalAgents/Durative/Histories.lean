import IntervalAgents.Durative.Examples

/-!
# Histories: swap classes, the review and release net, and the absence of a least repair

* The three non-representable histories of `Examples.lean` are single swap classes.
* The review and release net (Example 4.13), read as a durative system: with histories taken as
  all runs between two configurations it is not representable; under swap classes it splits into
  two representable histories.
* A three-action committed system with over-all conditions in which three incomparable conflict
  extensions each restore homogeneous step conservativity: Part B has no least repair.
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

namespace IntervalAgents
namespace Three

open GAS (Ev)
open DAS

/-! ### The three histories are single swap classes -/

theorem beginBegin_single_class :
    let H := history beginBegin X3 ((true, true), ∅) ((false, false), ∅)
    (swapClass H (H.headD [])).length = 15 ∧ H.all (fun w => decide (w ∈ swapClass H (H.headD []))) = true := by
  decide
theorem endEnd_single_class :
    let H := history endEnd X3 (true, ∅) (false, ∅)
    (swapClass H (H.headD [])).length = 45 ∧ H.all (fun w => decide (w ∈ swapClass H (H.headD []))) = true := by
  decide
theorem disjunctive_history_size :
    (history disjunctive X3 ((false, false, true), ∅) ((true, true, false), ∅)).length = 81 := by decide
theorem disjunctive_single_class :
    let H := history disjunctive X3 ((false, false, true), ∅) ((true, true, false), ∅)
    (swapClass H (H.headD [])).length = 81 ∧ H.all (fun w => decide (w ∈ swapClass H (H.headD []))) = true := by
  decide

/-! ### Systems with a conflict relation -/

/-- Build a three-action system with a Boolean conflict relation; commutation is required for
non-conflicting pairs only. -/
def mkc {St : Type} (start over stop : Three → St → Bool) (acq rel : Three → St → St)
    (conf : Three → Three → Bool) (hsymm : ∀ x y, conf x y = conf y x)
    (hacq : ∀ x y s, x ≠ y → conf x y = false → acq x (acq y s) = acq y (acq x s))
    (hrel : ∀ x y s, x ≠ y → conf x y = false → rel x (rel y s) = rel y (rel x s))
    (hmix : ∀ x y s, x ≠ y → conf x y = false → acq x (rel y s) = rel y (acq x s)) : DAS St Three where
  start := fun x s => start x s = true
  over := fun x s => over x s = true
  stop := fun x s => stop x s = true
  acq := acq
  rel := rel
  conflict := fun x y => conf x y = true
  conflict_symm := fun x y h => by rw [hsymm]; exact h
  acq_acq := fun x y hxy hnc s => hacq x y s hxy (by simpa using hnc)
  rel_rel := fun x y hxy hnc s => hrel x y s hxy (by simpa using hnc)
  acq_rel := fun x y hxy hnc s => hmix x y s hxy (by simpa using hnc)

instance decStartC {St : Type} (start over stop : Three → St → Bool) (acq rel) conf h0 h1 h2 h3 :
    ∀ x s, Decidable ((mkc start over stop acq rel conf h0 h1 h2 h3).start x s) :=
  fun x s => inferInstanceAs (Decidable (start x s = true))
instance decOverC {St : Type} (start over stop : Three → St → Bool) (acq rel) conf h0 h1 h2 h3 :
    ∀ x s, Decidable ((mkc start over stop acq rel conf h0 h1 h2 h3).over x s) :=
  fun x s => inferInstanceAs (Decidable (over x s = true))
instance decStopC {St : Type} (start over stop : Three → St → Bool) (acq rel) conf h0 h1 h2 h3 :
    ∀ x s, Decidable ((mkc start over stop acq rel conf h0 h1 h2 h3).stop x s) :=
  fun x s => inferInstanceAs (Decidable (stop x s = true))
instance decConflictC {St : Type} (start over stop : Three → St → Bool) (acq rel) conf h0 h1 h2 h3 :
    ∀ x y, Decidable ((mkc start over stop acq rel conf h0 h1 h2 h3).conflict x y) :=
  fun x y => inferInstanceAs (Decidable (conf x y = true))

/-! ### The review and release net as a durative system

Places `(s1, s2, s3, s4, s5)`; `t0` submits (`s1` to `s3`), `t1` reviews (`s3` to `s5`),
`t2` releases (`s2` to `s4`) unless `s3` is marked. `t0` and `t1` share `s3` and conflict. -/

abbrev M5 := Bool × Bool × Bool × Bool × Bool

def fig1Conf : Three → Three → Bool
  | .t0, .t1 => true
  | .t1, .t0 => true
  | _, _ => false

abbrev fig1 : DAS M5 Three :=
  mkc (start := fun x s => match x with
      | .t0 => s.1 && !s.2.2.1
      | .t1 => s.2.2.1 && !s.2.2.2.2
      | .t2 => s.2.1 && !s.2.2.2.1 && !s.2.2.1)
    (over := fun _ _ => true) (stop := fun _ _ => true) (acq := fun _ s => s)
    (rel := fun x s => match x with
      | .t0 => (false, s.2.1, true, s.2.2.2.1, s.2.2.2.2)
      | .t1 => (s.1, s.2.1, false, s.2.2.2.1, true)
      | .t2 => (s.1, false, s.2.2.1, true, s.2.2.2.2))
    fig1Conf (by intro x y; cases x <;> cases y <;> rfl)
    (by intro x y s _ _; rfl)
    (by intro x y s hxy hc; obtain ⟨s1, s2, s3, s4, s5⟩ := s
        cases x <;> cases y <;> first | rfl | exact absurd hc (by decide))
    (by intro x y s _ _; rfl)

/-- The history of Example 4.14 under the committed discipline: ten runs. -/
theorem fig1_history_size :
    (history fig1 X3 ((true, true, false, false, false), ∅) ((false, false, false, true, true), ∅)).length = 10 := by
  decide

/-- With histories taken as all runs between two configurations, the review and release net is
not representable: the serial order submit, release, review extends the invariant structure but
is not a run. -/
theorem fig1_not_representable :
    representable X3 (history fig1 X3 ((true, true, false, false, false), ∅) ((false, false, false, true, true), ∅)) = false := by
  decide

/-- Under swap classes the same ten runs split into two histories, of one and nine runs, both
representable. -/
theorem fig1_two_classes :
    let H := history fig1 X3 ((true, true, false, false, false), ∅) ((false, false, false, true, true), ∅)
    let C1 := swapClass H [Ev.B t0, Ev.E t0, Ev.B t1, Ev.E t1, Ev.B t2, Ev.E t2]
    let C2 := swapClass H [Ev.B t0, Ev.B t2, Ev.E t0, Ev.B t1, Ev.E t1, Ev.E t2]
    C1.length = 1 ∧ C2.length = 9 ∧ H.all (fun w => decide (w ∈ C1 ∨ w ∈ C2)) = true ∧
      representable X3 C1 = true ∧ representable X3 C2 = true := by
  decide

/-! ### No least repair in Part B

Three independent committed actions on a counter `n` in `{0, 1, 2}`: each requires `n ≤ 1` at its
start and over all, and each ending increments `n` (capped at 2). With all three in flight at
`n = 0`, every ending is enabled but after one ending the others are blocked, so endings are not
transparent. Adding any one conflict restores transparency, and the three repairs are
incomparable. -/

def incr (n : Fin 3) : Fin 3 := if n.val = 0 then 1 else 2

abbrev nlr (conf : Three → Three → Bool) (hsymm : ∀ x y, conf x y = conf y x) : DAS (Fin 3) Three :=
  mkc (start := fun _ n => decide (n.val ≤ 1)) (over := fun _ n => decide (n.val ≤ 1))
    (stop := fun _ _ => true) (acq := fun _ n => n) (rel := fun _ n => incr n) conf hsymm
    (by intro x y s _ _; rfl) (by intro x y s _ _; rfl) (by intro x y s _ _; rfl)

abbrev nlr0 : DAS (Fin 3) Three := nlr (fun _ _ => false) (by intro x y; rfl)
abbrev nlrAB : DAS (Fin 3) Three := nlr (fun x y => match x, y with | .t0, .t1 => true | .t1, .t0 => true | _, _ => false)
  (by intro x y; cases x <;> cases y <;> rfl)
abbrev nlrAC : DAS (Fin 3) Three := nlr (fun x y => match x, y with | .t0, .t2 => true | .t2, .t0 => true | _, _ => false)
  (by intro x y; cases x <;> cases y <;> rfl)
abbrev nlrBC : DAS (Fin 3) Three := nlr (fun x y => match x, y with | .t1, .t2 => true | .t2, .t1 => true | _, _ => false)
  (by intro x y; cases x <;> cases y <;> rfl)

theorem nlr0_not_ET_EE : ¬ nlr0.ET_EE := by decide
theorem nlr0_not_hsc : ¬ nlr0.HSC := nlr0.not_hsc_of_not_ET_EE nlr0_not_ET_EE
theorem nlrAB_hsc : nlrAB.HSC := nlrAB.hsc_of_et (by decide) (by decide)
theorem nlrAC_hsc : nlrAC.HSC := nlrAC.hsc_of_et (by decide) (by decide)
theorem nlrBC_hsc : nlrBC.HSC := nlrBC.hsc_of_et (by decide) (by decide)


end Three
end IntervalAgents
