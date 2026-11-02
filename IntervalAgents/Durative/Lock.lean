import IntervalAgents.Durative.Characterization

/-!
# The committed discipline and over-all conditions: the lock theorem

Under the committed discipline (`acq a = id`) beginnings are transparent to independent
beginnings whatever the conditions are. With over-all conditions the remaining question is
the transparency of endings, and the clean sufficient condition is the *lock condition*: no
ending of an independent action falsifies the over-all condition of an action in flight.
For two actions in flight the exact condition is that interference, if any, is mutual.
Adding a conflict on every interfering pair restores homogeneous step conservativity.
-/

set_option linter.unusedSectionVars false

namespace IntervalAgents
namespace DAS

open GAS (Ev)

variable {S A : Type} [DecidableEq A] (D : DAS S A)

/-- The committed discipline: nothing is published when an action begins. -/
def Committed : Prop := ∀ a t, D.acq a t = t

/-- No at-end conditions (the pure over-all reading). -/
def NoEndConditions : Prop := ∀ a t, D.stop a t

/-- Under the committed discipline, beginnings are transparent to independent beginnings. -/
theorem committed_ET_BB (hc : D.Committed) : D.ET_BB := by
  have hc' : ∀ a t, D.acq a t = t := hc
  intro c _ a b hab hena
  obtain ⟨t, F⟩ := c
  obtain ⟨-, -, -, hoa, -⟩ := hena
  rw [hc' a t] at hoa
  simp only [enB, nextB, hc', Finset.mem_insert, not_or]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨⟨fun e => hab.1 e.symm, h1⟩, ?_, h3, h4, ?_⟩
    · intro d hd
      rcases hd with rfl | hd'
      · exact fun h => hab.2 (D.conflict_symm _ _ h)
      · exact h2 d hd'
    · intro d hd
      rcases hd with rfl | hd'
      · exact hoa
      · exact h5 d hd'
  · rintro ⟨⟨-, h1⟩, h2, h3, h4, h5⟩
    exact ⟨h1, fun d hd => h2 d (Or.inr hd), h3, h4, fun d hd => h5 d (Or.inr hd)⟩

/-- The lock condition: no ending of an independent action that can end falsifies the
over-all condition of an action in flight. -/
def Lock : Prop :=
  ∀ a b, D.Indep a b → ∀ t, D.over a t → D.over b t → D.stop b t → D.over a (D.rel b t)

/-- Under the lock condition and without at-end conditions, endings are transparent to each
other. -/
theorem lock_ET_EE (hL : D.Lock) (hs : D.NoEndConditions) : D.ET_EE := by
  have hs' : ∀ a t, D.stop a t := hs
  intro c hc a b hab hena
  obtain ⟨t, F⟩ := c
  obtain ⟨hpw, hov⟩ := hc
  obtain ⟨haF, -, hoth⟩ := hena
  simp only [enE, nextE, hs', true_and]
  constructor
  · rintro ⟨hbF, -⟩
    refine ⟨Finset.mem_erase.2 ⟨Ne.symm hab, hbF⟩, ?_⟩
    intro d hd hdb
    have hdF := Finset.mem_of_mem_erase hd
    have hda := Finset.ne_of_mem_erase hd
    exact hL d b (hpw d hdF b hbF hdb) (D.rel a t) (hoth d hdF hda) (hoth b hbF (Ne.symm hab)) (hs b _)
  · rintro ⟨hbF', -⟩
    have hbF := Finset.mem_of_mem_erase hbF'
    refine ⟨hbF, ?_⟩
    intro d hdF hdb
    exact hL d b (hpw d hdF b hbF hdb) t (hov d hdF) (hov b hbF) (hs b t)

/-- **Theorem (lock).** Committed discipline, over-all conditions, lock condition: the system
is homogeneous-step conservative. -/
theorem lock_hsc (hc : D.Committed) (hL : D.Lock) (hs : D.NoEndConditions) : D.HSC :=
  D.hsc_of_et (D.committed_ET_BB hc) (D.lock_ET_EE hL hs)

/-- The clause of `ET_EE` at one configuration for one ordered pair. -/
def ETEEat (c : Config S A) (a b : A) : Prop := D.enE a c → (D.enE b c ↔ D.enE b (D.nextE a c))

/-- **Two actions in flight.** Without at-end conditions, the two clauses of `ET_EE` at a
configuration with exactly `a` and `b` in flight say that interference between their endings
is mutual or absent. -/
theorem two_inflight_iff (hs : D.NoEndConditions) {a b : A} (hab : a ≠ b) (t : S) :
    (D.ETEEat (t, {a, b}) a b ∧ D.ETEEat (t, {a, b}) b a) ↔
      (D.over b (D.rel a t) ↔ D.over a (D.rel b t)) := by
  have hs' : ∀ a t, D.stop a t := hs
  have hba : b ≠ a := Ne.symm hab
  have e1 : D.enE a (t, {a, b}) ↔ D.over b (D.rel a t) := by
    simp [enE, hs', hab, hba]
  have e2 : D.enE b (t, {a, b}) ↔ D.over a (D.rel b t) := by
    simp [enE, hs', hab, hba]
  have e3 : D.enE b (D.nextE a (t, {a, b})) := by
    simp [nextE, enE, hs', hab]
  have e4 : D.enE a (D.nextE b (t, {a, b})) := by
    simp [nextE, enE, hs', hab]
    intro d h1 hd h2
    rcases hd with rfl | rfl <;> simp_all
  simp only [ETEEat, e1, e2, e3, e4, iff_true]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩

/-! ## The repair -/

/-- Two actions interfere when, with both in flight, one ending can falsify the other's
over-all condition. -/
def Interferes (a b : A) : Prop :=
  ∃ t, D.over a t ∧ D.over b t ∧ (¬ D.over a (D.rel b t) ∨ ¬ D.over b (D.rel a t))

theorem interferes_symm {a b : A} (h : D.Interferes a b) : D.Interferes b a := by
  obtain ⟨t, h1, h2, h3⟩ := h
  exact ⟨t, h2, h1, h3.symm⟩

/-- The same system with a conflict added on every interfering pair. -/
def repair : DAS S A where
  start := D.start
  over := D.over
  stop := D.stop
  acq := D.acq
  rel := D.rel
  conflict := fun a b => D.conflict a b ∨ D.Interferes a b
  conflict_symm := fun a b h => h.elim (fun h => Or.inl (D.conflict_symm a b h))
    (fun h => Or.inr (D.interferes_symm h))
  acq_acq := fun a b hne hnc => D.acq_acq a b hne (fun h => hnc (Or.inl h))
  rel_rel := fun a b hne hnc => D.rel_rel a b hne (fun h => hnc (Or.inl h))
  acq_rel := fun a b hne hnc => D.acq_rel a b hne (fun h => hnc (Or.inl h))

theorem repair_lock : D.repair.Lock := by
  intro a b hab t hoa hob _
  by_contra hcon
  exact hab.2 (Or.inr ⟨t, hoa, hob, Or.inl hcon⟩)

/-- **Corollary (least repair).** Adding a conflict on every interfering pair of a committed
system with over-all conditions makes it homogeneous-step conservative. -/
theorem repair_hsc (hc : D.Committed) (hs : D.NoEndConditions) : D.repair.HSC :=
  D.repair.lock_hsc hc D.repair_lock hs

end DAS
end IntervalAgents
