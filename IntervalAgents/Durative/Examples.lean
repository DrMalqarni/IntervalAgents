import IntervalAgents.Durative.Exec
import IntervalAgents.Durative.Bridge

/-!
# Witnesses for Part B

* The two sound cells of the classification table, as general theorems:
  committed discipline with at-start conditions, start-only discipline with at-end conditions.
* A two-action counterexample for every other cell (decided by `decide`).
* Required concurrency: a two-action witness for each kind of temporal gap.
* Structures: histories that no structure of precedence and weak precedence represents,
  one produced by a begin-begin constraint (consuming discipline), one by an end-end
  constraint (over-all condition under the committed discipline).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

namespace IntervalAgents
namespace DAS

open GAS (Ev)

variable {S A : Type} [DecidableEq A] (D : DAS S A)

/-! ## The two sound cells -/

/-- Without over-all and at-end conditions, endings are transparent to each other. -/
theorem trivial_ET_EE (ho : ∀ a t, D.over a t) (hs : ∀ a t, D.stop a t) : D.ET_EE := by
  intro c _ a b hab _
  obtain ⟨t, F⟩ := c
  simp only [enE, nextE, ho, hs, implies_true, and_true]
  exact ⟨fun h => Finset.mem_erase.2 ⟨Ne.symm hab, h⟩, fun h => Finset.mem_of_mem_erase h⟩

/-- **Committed discipline, at-start conditions**: always homogeneous-step conservative. -/
theorem committed_atStart_hsc (hc : D.Committed) (ho : ∀ a t, D.over a t) (hs : ∀ a t, D.stop a t) :
    D.HSC :=
  D.hsc_of_et (D.committed_ET_BB hc) (D.trivial_ET_EE ho hs)

/-- The start-only discipline: nothing is published when an action ends. -/
def StartOnly : Prop := ∀ a t, D.rel a t = t

/-- Without start and over-all conditions, beginnings are transparent to independent
beginnings. -/
theorem trivial_ET_BB (hst : ∀ a t, D.start a t) (ho : ∀ a t, D.over a t) : D.ET_BB := by
  intro c _ a b hab _
  obtain ⟨t, F⟩ := c
  simp only [enB, nextB, hst, ho, implies_true, and_true, Finset.mem_insert, not_or]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun e => hab.1 e.symm, h1⟩, ?_⟩
    intro d hd
    rcases hd with rfl | hd'
    · exact fun h => hab.2 (D.conflict_symm _ _ h)
    · exact h2 d hd'
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨h1, fun d hd => h2 d (Or.inr hd)⟩

/-- Under the start-only discipline, endings are transparent to each other whatever the at-end
conditions, provided there are no over-all conditions. -/
theorem startOnly_ET_EE (hr : D.StartOnly) (ho : ∀ a t, D.over a t) : D.ET_EE := by
  have hr' : ∀ a t, D.rel a t = t := hr
  intro c _ a b hab _
  obtain ⟨t, F⟩ := c
  simp only [enE, nextE, ho, hr', implies_true, and_true]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨Finset.mem_erase.2 ⟨Ne.symm hab, h1⟩, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨Finset.mem_of_mem_erase h1, h2⟩

/-- **Start-only discipline, at-end conditions**: always homogeneous-step conservative. -/
theorem startOnly_atEnd_hsc (hr : D.StartOnly) (hst : ∀ a t, D.start a t) (ho : ∀ a t, D.over a t) :
    D.HSC :=
  D.hsc_of_et (D.trivial_ET_BB hst ho) (D.startOnly_ET_EE hr ho)

end DAS

/-! ## Two-action counterexamples for the other cells

All systems below have two actions `a`, `b` on a state of one or two Boolean variables, with
no conflicts. -/

inductive Two | a | b
  deriving DecidableEq

instance : Fintype Two := ⟨{Two.a, Two.b}, fun x => by cases x <;> simp⟩

namespace Two

open GAS (Ev)

/-- Build a two-action system from Boolean-valued conditions and effects. The commutation
obligations are discharged by case analysis. -/
def mk {St : Type} (start over stop : Two → St → Bool) (acq rel : Two → St → St)
    (h1 : ∀ s, acq .a (acq .b s) = acq .b (acq .a s))
    (h2 : ∀ s, rel .a (rel .b s) = rel .b (rel .a s))
    (h3 : ∀ s, acq .a (rel .b s) = rel .b (acq .a s))
    (h4 : ∀ s, acq .b (rel .a s) = rel .a (acq .b s)) : DAS St Two where
  start := fun x s => start x s = true
  over := fun x s => over x s = true
  stop := fun x s => stop x s = true
  acq := acq
  rel := rel
  conflict := fun _ _ => False
  conflict_symm := fun _ _ h => h
  acq_acq := by
    intro x y hxy _ s
    cases x <;> cases y
    · exact absurd rfl hxy
    · exact h1 s
    · exact (h1 s).symm
    · exact absurd rfl hxy
  rel_rel := by
    intro x y hxy _ s
    cases x <;> cases y
    · exact absurd rfl hxy
    · exact h2 s
    · exact (h2 s).symm
    · exact absurd rfl hxy
  acq_rel := by
    intro x y hxy _ s
    cases x <;> cases y
    · exact absurd rfl hxy
    · exact h3 s
    · exact h4 s
    · exact absurd rfl hxy

instance decStart {St : Type} (start over stop : Two → St → Bool) (acq rel) h1 h2 h3 h4 :
    ∀ x s, Decidable ((mk start over stop acq rel h1 h2 h3 h4).start x s) :=
  fun x s => inferInstanceAs (Decidable (start x s = true))
instance decOver {St : Type} (start over stop : Two → St → Bool) (acq rel) h1 h2 h3 h4 :
    ∀ x s, Decidable ((mk start over stop acq rel h1 h2 h3 h4).over x s) :=
  fun x s => inferInstanceAs (Decidable (over x s = true))
instance decStop {St : Type} (start over stop : Two → St → Bool) (acq rel) h1 h2 h3 h4 :
    ∀ x s, Decidable ((mk start over stop acq rel h1 h2 h3 h4).stop x s) :=
  fun x s => inferInstanceAs (Decidable (stop x s = true))
instance decConflict {St : Type} (start over stop : Two → St → Bool) (acq rel) h1 h2 h3 h4 :
    ∀ x y, Decidable ((mk start over stop acq rel h1 h2 h3 h4).conflict x y) :=
  fun _ _ => inferInstanceAs (Decidable False)

/-- `p` is the single Boolean variable. -/
abbrev St1 := Bool

/-- The two actions `a`, `b` of Proposition 7.4 on their own: `a` reads `p` at its start and over
all, `b` reads `p` at its start and consumes it when it ends. Their history from `p` marked has
three runs, is representable, and is not closed: `B a B b E b E a` has the interval order of
`B a B b E a E b` but is not a run. -/
abbrev endEndAB : DAS St1 Two :=
  mk (start := fun _ p => p) (over := fun x p => match x with | .a => p | .b => true)
    (stop := fun _ _ => true) (acq := fun _ p => p)
    (rel := fun x p => match x with | .a => p | .b => false)
    (fun _ => rfl) (fun s => by cases s <;> rfl) (fun _ => rfl) (fun _ => rfl)

theorem endEndAB_history_size :
    (DAS.history endEndAB [Two.a, Two.b] (true, ∅) (false, ∅)).length = 3 := by decide
theorem endEndAB_representable :
    DAS.representable [Two.a, Two.b] (DAS.history endEndAB [Two.a, Two.b] (true, ∅) (false, ∅)) = true := by
  decide
theorem endEndAB_not_closed :
    DAS.closed [Two.a, Two.b] (DAS.history endEndAB [Two.a, Two.b] (true, ∅) (false, ∅)) = false := by
  decide

/-- Committed discipline, over-all condition: `a` reads `p` over all, `b` consumes `p` when it
ends (the revocation trace). -/
abbrev committedOverall : DAS St1 Two :=
  mk (start := fun _ p => p) (over := fun _ p => p)
    (stop := fun _ _ => true) (acq := fun _ p => p)
    (rel := fun x p => match x with | .a => p | .b => false)
    (fun _ => rfl) (fun s => by cases s <;> rfl) (fun _ => rfl) (fun _ => rfl)

theorem committedOverall_committed : committedOverall.Committed := fun _ _ => rfl
theorem committedOverall_noEnd : committedOverall.NoEndConditions := fun _ _ => rfl
theorem committedOverall_not_ET_EE : ¬ committedOverall.ET_EE := by decide
theorem committedOverall_not_hsc : ¬ committedOverall.HSC :=
  fun h => committedOverall_not_ET_EE (committedOverall.et_of_hsc h).2
/-- The run "a ends, then b ends" exists from the configuration with both in flight, but
"b ends, then a ends" does not: the run set is not closed under swapping endings. -/
theorem committedOverall_not_J_EE : ¬ committedOverall.J_EE := by
  intro h
  have := h (true, {Two.a, Two.b}) (by decide) Two.a Two.b (false, ∅) (by decide) (by decide)
  revert this; decide
theorem committedOverall_not_lock : ¬ committedOverall.Lock := by decide
theorem committedOverall_not_jsound : ¬ committedOverall.JSound :=
  committedOverall.not_jsound_of_not_J_EE committedOverall_not_J_EE

/-- Committed discipline, at-end condition: `a` needs `p` when it ends, `b` clears `p` when it
ends. -/
abbrev committedAtEnd : DAS St1 Two :=
  mk (start := fun _ _ => true) (over := fun _ _ => true)
    (stop := fun x p => match x with | .a => p | .b => true) (acq := fun _ p => p)
    (rel := fun x p => match x with | .a => p | .b => false)
    (fun _ => rfl) (fun s => by cases s <;> rfl) (fun _ => rfl) (fun _ => rfl)

theorem committedAtEnd_not_ET_EE : ¬ committedAtEnd.ET_EE := by decide
theorem committedAtEnd_not_hsc : ¬ committedAtEnd.HSC :=
  fun h => committedAtEnd_not_ET_EE (committedAtEnd.et_of_hsc h).2
theorem committedAtEnd_not_J_EE : ¬ committedAtEnd.J_EE := by
  intro h
  have := h (true, {Two.a, Two.b}) (by decide) Two.a Two.b (false, ∅) (by decide) (by decide)
  revert this; decide
theorem committedAtEnd_not_jsound : ¬ committedAtEnd.JSound :=
  committedAtEnd.not_jsound_of_not_J_EE committedAtEnd_not_J_EE

/-- Start-only discipline, at-start condition: `a` reads `p` when it begins, `b` clears `p`
when it begins (Janicki's activator net AN0). -/
abbrev startOnlyAtStart : DAS St1 Two :=
  mk (start := fun x p => match x with | .a => p | .b => true) (over := fun _ _ => true)
    (stop := fun _ _ => true) (acq := fun x p => match x with | .a => p | .b => false)
    (rel := fun _ p => p)
    (fun s => by cases s <;> rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem startOnlyAtStart_not_ET_BB : ¬ startOnlyAtStart.ET_BB := by decide
theorem startOnlyAtStart_not_hsc : ¬ startOnlyAtStart.HSC :=
  fun h => startOnlyAtStart_not_ET_BB (startOnlyAtStart.et_of_hsc h).1
theorem startOnlyAtStart_not_J_BB : ¬ startOnlyAtStart.J_BB := by
  intro h
  have := h (true, ∅) (by decide) Two.a Two.b (false, {Two.a, Two.b}) (by decide) (by decide)
  revert this; decide
theorem startOnlyAtStart_not_jsound : ¬ startOnlyAtStart.JSound :=
  startOnlyAtStart.not_jsound_of_not_J_BB startOnlyAtStart_not_J_BB

/-- Start-only discipline, over-all condition: `a` requires `p` to be absent at its start and
over all; `b` clears `p` when it begins. From `p` present, `b` then `a` runs but `a` then `b`
cannot start. -/
abbrev startOnlyOverall : DAS St1 Two :=
  mk (start := fun x p => match x with | .a => !p | .b => true)
    (over := fun x p => match x with | .a => !p | .b => true)
    (stop := fun _ _ => true) (acq := fun x p => match x with | .a => p | .b => false)
    (rel := fun _ p => p)
    (fun s => by cases s <;> rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem startOnlyOverall_not_ET_BB : ¬ startOnlyOverall.ET_BB := by decide
theorem startOnlyOverall_not_hsc : ¬ startOnlyOverall.HSC :=
  fun h => startOnlyOverall_not_ET_BB (startOnlyOverall.et_of_hsc h).1
theorem startOnlyOverall_not_J_BB : ¬ startOnlyOverall.J_BB := by
  intro h
  have := h (true, ∅) (by decide) Two.b Two.a (false, {Two.a, Two.b}) (by decide) (by decide)
  revert this; decide
theorem startOnlyOverall_not_jsound : ¬ startOnlyOverall.JSound :=
  startOnlyOverall.not_jsound_of_not_J_BB startOnlyOverall_not_J_BB

/-- Two Boolean variables `(p, q)`. -/
abbrev St2 := Bool × Bool

/-- Consuming discipline, at-start condition: `a` reads `p` when it begins; `b` consumes `p`
when it begins and produces `q` when it ends. -/
abbrev consumingAtStart : DAS St2 Two :=
  mk (start := fun x s => match x with | .a => s.1 | .b => true) (over := fun _ _ => true)
    (stop := fun _ _ => true) (acq := fun x s => match x with | .a => s | .b => (false, s.2))
    (rel := fun x s => match x with | .a => s | .b => (s.1, true))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem consumingAtStart_not_ET_BB : ¬ consumingAtStart.ET_BB := by decide
theorem consumingAtStart_not_hsc : ¬ consumingAtStart.HSC :=
  fun h => consumingAtStart_not_ET_BB (consumingAtStart.et_of_hsc h).1
theorem consumingAtStart_not_J_BB : ¬ consumingAtStart.J_BB := by
  intro h
  have := h ((true, false), ∅) (by decide) Two.a Two.b ((false, false), {Two.a, Two.b}) (by decide) (by decide)
  revert this; decide
theorem consumingAtStart_not_jsound : ¬ consumingAtStart.JSound :=
  consumingAtStart.not_jsound_of_not_J_BB consumingAtStart_not_J_BB

/-- Consuming discipline, over-all condition: `a` requires `p` absent at its start and over all;
`b` clears `p` when it begins and sets `q` when it ends. -/
abbrev consumingOverall : DAS St2 Two :=
  mk (start := fun x s => match x with | .a => !s.1 | .b => true)
    (over := fun x s => match x with | .a => !s.1 | .b => true)
    (stop := fun _ _ => true) (acq := fun x s => match x with | .a => s | .b => (false, s.2))
    (rel := fun x s => match x with | .a => s | .b => (s.1, true))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem consumingOverall_not_ET_BB : ¬ consumingOverall.ET_BB := by decide
theorem consumingOverall_not_hsc : ¬ consumingOverall.HSC :=
  fun h => consumingOverall_not_ET_BB (consumingOverall.et_of_hsc h).1
theorem consumingOverall_not_J_BB : ¬ consumingOverall.J_BB := by
  intro h
  have := h ((true, false), ∅) (by decide) Two.b Two.a ((false, false), {Two.a, Two.b}) (by decide) (by decide)
  revert this; decide
theorem consumingOverall_not_jsound : ¬ consumingOverall.JSound :=
  consumingOverall.not_jsound_of_not_J_BB consumingOverall_not_J_BB

/-- Consuming discipline, at-end condition: `a` needs `q` false when it ends; `b` consumes `p`
when it begins and produces `q` when it ends. -/
abbrev consumingAtEnd : DAS St2 Two :=
  mk (start := fun _ _ => true) (over := fun _ _ => true)
    (stop := fun x s => match x with | .a => !s.2 | .b => true)
    (acq := fun x s => match x with | .a => s | .b => (false, s.2))
    (rel := fun x s => match x with | .a => s | .b => (s.1, true))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem consumingAtEnd_not_ET_EE : ¬ consumingAtEnd.ET_EE := by decide
theorem consumingAtEnd_not_hsc : ¬ consumingAtEnd.HSC :=
  fun h => consumingAtEnd_not_ET_EE (consumingAtEnd.et_of_hsc h).2
theorem consumingAtEnd_not_J_EE : ¬ consumingAtEnd.J_EE := by
  intro h
  have := h ((false, false), {Two.a, Two.b}) (by decide) Two.a Two.b ((false, true), ∅) (by decide) (by decide)
  revert this; decide
theorem consumingAtEnd_not_jsound : ¬ consumingAtEnd.JSound :=
  consumingAtEnd.not_jsound_of_not_J_EE consumingAtEnd_not_J_EE

/-! ## Required concurrency: one witness per kind of temporal gap -/

/-- Start conditions with end effects: each action's end effect disables the other's start
condition (`a` needs `q` false and sets `p`; `b` needs `p` false and sets `q`). -/
abbrev gapStartEnd : DAS St2 Two :=
  mk (start := fun x s => match x with | .a => !s.2 | .b => !s.1) (over := fun _ _ => true)
    (stop := fun _ _ => true) (acq := fun _ s => s)
    (rel := fun x s => match x with | .a => (true, s.2) | .b => (s.1, true))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem gapStartEnd_int : gapStartEnd.IntReach (false, false) (true, true) :=
  ⟨[Ev.B .a, Ev.B .b, Ev.E .a, Ev.E .b], by decide⟩
theorem gapStartEnd_notSeq : ¬ gapStartEnd.SeqReach (false, false) (true, true) := by
  intro h
  have := gapStartEnd.seqReach_inv (fun s => ¬ (s.1 = true ∧ s.2 = true)) (by decide) (by decide) h
  exact this ⟨rfl, rfl⟩

/-- End conditions with start effects: each action's start effect enables the other's end
condition (`a` sets `p` and needs `q` to end; `b` sets `q` and needs `p` to end). -/
abbrev gapEndStart : DAS St2 Two :=
  mk (start := fun _ _ => true) (over := fun _ _ => true)
    (stop := fun x s => match x with | .a => s.2 | .b => s.1)
    (acq := fun x s => match x with | .a => (true, s.2) | .b => (s.1, true))
    (rel := fun _ s => s)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem gapEndStart_int : gapEndStart.IntReach (false, false) (true, true) :=
  ⟨[Ev.B .a, Ev.B .b, Ev.E .a, Ev.E .b], by decide⟩
theorem gapEndStart_notSeq : ¬ gapEndStart.SeqReach (false, false) (true, true) := by
  intro h
  have := gapEndStart.seqReach_inv (fun s => s = (false, false)) rfl (by decide) h
  cases this

/-- Effects at both ends: `a` sets `p` when it begins and clears it when it ends; `b` needs `p`
when it begins and sets `q` when it ends (a condition that holds only while `a` is in flight). -/
abbrev gapBothEnds : DAS St2 Two :=
  mk (start := fun x s => match x with | .a => true | .b => s.1) (over := fun _ _ => true)
    (stop := fun _ _ => true)
    (acq := fun x s => match x with | .a => (true, s.2) | .b => s)
    (rel := fun x s => match x with | .a => (false, s.2) | .b => (s.1, true))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem gapBothEnds_int : gapBothEnds.IntReach (false, false) (false, true) :=
  ⟨[Ev.B .a, Ev.B .b, Ev.E .a, Ev.E .b], by decide⟩
theorem gapBothEnds_notSeq : ¬ gapBothEnds.SeqReach (false, false) (false, true) := by
  intro h
  have := gapBothEnds.seqReach_inv (fun s => s = (false, false)) rfl (by decide) h
  cases this

/-- As `gapBothEnds`, with the condition of `b` read over all. -/
abbrev gapBothEndsOverall : DAS St2 Two :=
  mk (start := fun x s => match x with | .a => true | .b => s.1)
    (over := fun x s => match x with | .a => true | .b => s.1)
    (stop := fun _ _ => true)
    (acq := fun x s => match x with | .a => (true, s.2) | .b => s)
    (rel := fun x s => match x with | .a => (false, s.2) | .b => (s.1, true))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem gapBothEndsOverall_int : gapBothEndsOverall.IntReach (false, false) (false, true) :=
  ⟨[Ev.B .a, Ev.B .b, Ev.E .b, Ev.E .a], by decide⟩
theorem gapBothEndsOverall_notSeq : ¬ gapBothEndsOverall.SeqReach (false, false) (false, true) := by
  intro h
  have := gapBothEndsOverall.seqReach_inv (fun s => s = (false, false)) rfl (by decide) h
  cases this

/-- As `gapBothEnds`, with the condition of `b` read at its end. -/
abbrev gapBothEndsAtEnd : DAS St2 Two :=
  mk (start := fun _ _ => true) (over := fun _ _ => true)
    (stop := fun x s => match x with | .a => true | .b => s.1)
    (acq := fun x s => match x with | .a => (true, s.2) | .b => s)
    (rel := fun x s => match x with | .a => (false, s.2) | .b => (s.1, true))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem gapBothEndsAtEnd_int : gapBothEndsAtEnd.IntReach (false, false) (false, true) :=
  ⟨[Ev.B .a, Ev.B .b, Ev.E .b, Ev.E .a], by decide⟩
theorem gapBothEndsAtEnd_notSeq : ¬ gapBothEndsAtEnd.SeqReach (false, false) (false, true) := by
  intro h
  have := gapBothEndsAtEnd.seqReach_inv (fun s => s = (false, false)) rfl (by decide) h
  cases this

end Two

/-! ## Structures: histories outside the framework of precedence and weak precedence -/

inductive Three | t0 | t1 | t2
  deriving DecidableEq

instance : Fintype Three := ⟨{Three.t0, Three.t1, Three.t2}, fun x => by cases x <;> simp⟩

namespace Three

open GAS (Ev)

def mk {St : Type} (start over stop : Three → St → Bool) (acq rel : Three → St → St)
    (hacq : ∀ x y s, x ≠ y → acq x (acq y s) = acq y (acq x s))
    (hrel : ∀ x y s, x ≠ y → rel x (rel y s) = rel y (rel x s))
    (hmix : ∀ x y s, x ≠ y → acq x (rel y s) = rel y (acq x s)) : DAS St Three where
  start := fun x s => start x s = true
  over := fun x s => over x s = true
  stop := fun x s => stop x s = true
  acq := acq
  rel := rel
  conflict := fun _ _ => False
  conflict_symm := fun _ _ h => h
  acq_acq := fun x y hxy _ s => hacq x y s hxy
  rel_rel := fun x y hxy _ s => hrel x y s hxy
  acq_rel := fun x y hxy _ s => hmix x y s hxy

instance decStart {St : Type} (start over stop : Three → St → Bool) (acq rel) h1 h2 h3 :
    ∀ x s, Decidable ((mk start over stop acq rel h1 h2 h3).start x s) :=
  fun x s => inferInstanceAs (Decidable (start x s = true))
instance decOver {St : Type} (start over stop : Three → St → Bool) (acq rel) h1 h2 h3 :
    ∀ x s, Decidable ((mk start over stop acq rel h1 h2 h3).over x s) :=
  fun x s => inferInstanceAs (Decidable (over x s = true))
instance decStop {St : Type} (start over stop : Three → St → Bool) (acq rel) h1 h2 h3 :
    ∀ x s, Decidable ((mk start over stop acq rel h1 h2 h3).stop x s) :=
  fun x s => inferInstanceAs (Decidable (stop x s = true))
instance decConflict {St : Type} (start over stop : Three → St → Bool) (acq rel) h1 h2 h3 :
    ∀ x y, Decidable ((mk start over stop acq rel h1 h2 h3).conflict x y) :=
  fun _ _ => inferInstanceAs (Decidable False)

open DAS

/-- The three actions, as the action list of the histories below. -/
abbrev X3 : List Three := [t0, t1, t2]

/-- Consuming discipline, at-start conditions: `t0` consumes `p` and `q` when it begins;
`t1` reads `p`; `t2` requires `q` to be empty. The beginnings are forced into the order
`t1`, `t0`, `t2`. -/
abbrev beginBegin : DAS (Bool × Bool) Three :=
  mk (start := fun x s => match x with | .t0 => s.1 && s.2 | .t1 => s.1 | .t2 => !s.2)
    (over := fun _ _ => true) (stop := fun _ _ => true)
    (acq := fun x s => match x with | .t0 => (false, false) | _ => s)
    (rel := fun _ s => s)
    (by intro x y s hxy; cases x <;> cases y <;> first | exact absurd rfl hxy | rfl)
    (by intro x y s _; rfl) (by intro x y s _; rfl)

theorem beginBegin_history_size :
    (history beginBegin X3 ((true, true), ∅) ((false, false), ∅)).length = 15 := by decide
theorem beginBegin_not_representable :
    representable X3 (history beginBegin X3 ((true, true), ∅) ((false, false), ∅)) = false := by decide

/-- Committed discipline, over-all condition: `a = t0` reads `p` over all; `b = t1` consumes
`p` when it ends; `c = t2` is unconstrained. `t0` must end before `t1` ends. -/
abbrev endEnd : DAS Bool Three :=
  mk (start := fun x p => match x with | .t0 => p | .t1 => p | .t2 => true)
    (over := fun x p => match x with | .t0 => p | _ => true) (stop := fun _ _ => true)
    (acq := fun _ p => p)
    (rel := fun x p => match x with | .t1 => false | _ => p)
    (by intro x y s _; rfl)
    (by intro x y s hxy; cases x <;> cases y <;> first | exact absurd rfl hxy | rfl)
    (by intro x y s _; rfl)

theorem endEnd_history_size : (history endEnd X3 (true, ∅) (false, ∅)).length = 45 := by decide
theorem endEnd_not_representable : representable X3 (history endEnd X3 (true, ∅) (false, ∅)) = false := by
  decide

/-- Committed discipline, at-start conditions, but a disjunctive condition: `t0` needs `q` or
`r`; `t1` clears `r` when it ends; `t2` sets `q` when it ends. The state is `(p, q, r)` with `p`
set by `t0`. The history from `r` marked merges two token-level histories (`t0` read `r`, or
`t0` read the `q` produced by `t2`) and is not representable, although the system is sound. -/
abbrev disjunctive : DAS (Bool × Bool × Bool) Three :=
  mk (start := fun x s => match x with | .t0 => s.2.1 || s.2.2 | _ => true)
    (over := fun _ _ => true) (stop := fun _ _ => true)
    (acq := fun _ s => s)
    (rel := fun x s => match x with
      | .t0 => (true, s.2.1, s.2.2) | .t1 => (s.1, s.2.1, false) | .t2 => (s.1, true, s.2.2))
    (by intro x y s _; rfl)
    (by intro x y s hxy; cases x <;> cases y <;> first | exact absurd rfl hxy | rfl)
    (by intro x y s _; rfl)

theorem disjunctive_hsc : disjunctive.HSC :=
  disjunctive.committed_atStart_hsc (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
theorem disjunctive_not_representable :
    representable X3 (history disjunctive X3 ((false, false, true), ∅) ((true, true, false), ∅)) = false := by
  decide


end Three

/-! ## Soundness is strictly weaker than transparency (at-start conditions) -/

namespace SoundNotTransparent

open GAS

/-- Two actions on the state `(x, y)`: `a` needs `y` false and sets `x` when it begins; `b`
needs `x` false and sets `y` when it begins. Each beginning disables the other, so the step
`{a, b}` fires but no interval word of it runs; still, no run can be swapped into an invalid
one. -/
abbrev G : GAS (Bool × Bool) Two where
  pre := fun x s => (match x with | .a => !s.2 | .b => !s.1) = true
  grd := fun _ _ => True
  acq := fun x s => match x with | .a => (true, s.2) | .b => (s.1, true)
  rel := fun _ s => s
  conflict := fun _ _ => False
  conflict_symm := fun _ _ h => h
  acq_acq := by intro x y hxy _ s; cases x <;> cases y <;> first | exact absurd rfl hxy | rfl
  rel_rel := by intro x y _ _ s; rfl
  acq_rel := by intro x y _ _ s; rfl

instance (t : Two) (s : Bool × Bool) : Decidable (G.en t s) :=
  inferInstanceAs (Decidable ((match t with | .a => !s.2 | .b => !s.1) = true ∧ True))
instance (t u : Two) : Decidable (G.conflict t u) := inferInstanceAs (Decidable False)
instance (t u : Two) : Decidable (G.Indep t u) := inferInstanceAs (Decidable (t ≠ u ∧ ¬ G.conflict t u))

theorem swapCond : G.SwapCond := by
  unfold GAS.SwapCond; decide
theorem not_transparent : ¬ G.Transparent := by
  unfold GAS.Transparent; decide
theorem not_conservative : ¬ G.Conservative :=
  fun h => not_transparent (G.transparent_iff_conservative.2 h)
theorem jsound : G.toDAS.JSound := (G.toDAS_jsound_iff).2 swapCond

end SoundNotTransparent
end IntervalAgents
