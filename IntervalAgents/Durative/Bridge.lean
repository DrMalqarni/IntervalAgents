import IntervalAgents.Durative.Characterization
import IntervalAgents.Characterization

/-!
# At-start conditions as a special case

A guarded action system of Part A is a durative system whose over-all and at-end conditions
are trivial. For such systems, transparency of beginnings to beginnings is exactly
acquire-transparency, transparency of endings is automatic, and so homogeneous step
conservativity coincides with the step-conservativity of Part A.
-/

set_option linter.unusedSectionVars false

namespace IntervalAgents

variable {S A : Type} [DecidableEq A]

open GAS (Ev)

/-- The durative system of a guarded action system: at-start conditions only. -/
def GAS.toDAS (G : GAS S A) : DAS S A where
  start := G.en
  over := fun _ _ => True
  stop := fun _ _ => True
  acq := G.acq
  rel := G.rel
  conflict := G.conflict
  conflict_symm := G.conflict_symm
  acq_acq := G.acq_acq
  rel_rel := G.rel_rel
  acq_rel := G.acq_rel

namespace GAS

variable (G : GAS S A)

theorem toDAS_indep (a b : A) : G.toDAS.Indep a b ↔ G.Indep a b := Iff.rfl

theorem toDAS_enB (b : A) (t : S) (F : Finset A) :
    G.toDAS.enB b (t, F) ↔ b ∉ F ∧ (∀ d ∈ F, ¬ G.conflict b d) ∧ G.en b t := by
  simp [DAS.enB, toDAS]

theorem toDAS_enE (b : A) (t : S) (F : Finset A) : G.toDAS.enE b (t, F) ↔ b ∈ F := by
  simp [DAS.enE, toDAS]

/-- Without end conditions, endings are transparent to each other. -/
theorem toDAS_ET_EE : G.toDAS.ET_EE := by
  intro c _ a b hab hena
  obtain ⟨t, F⟩ := c
  simp only [DAS.nextE, toDAS_enE]
  exact ⟨fun h => Finset.mem_erase.2 ⟨Ne.symm hab, h⟩, fun h => Finset.mem_of_mem_erase h⟩

/-- For at-start conditions, transparency of beginnings is acquire-transparency. -/
theorem toDAS_ET_BB_iff : G.toDAS.ET_BB ↔ G.Transparent := by
  constructor
  · intro h a b hab t hat
    have hc : G.toDAS.Coherent (t, ∅) := ⟨by simp, by simp⟩
    have hena : G.toDAS.enB a (t, ∅) := (G.toDAS_enB a t ∅).2 ⟨by simp, by simp, hat⟩
    have key := h (t, ∅) hc a b hab hena
    simp only [DAS.nextB, toDAS_enB] at key
    have hnc : ¬ G.conflict b a := fun c => hab.2 (G.conflict_symm _ _ c)
    have hacq : G.toDAS.acq a t = G.acq a t := rfl
    simpa [hab.1.symm, hnc, hacq] using key
  · intro hT c _ a b hab hena
    obtain ⟨t, F⟩ := c
    rw [toDAS_enB] at hena
    simp only [DAS.nextB, toDAS_enB, Finset.mem_insert, not_or]
    have hbt := hT a b hab t hena.2.2
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨fun e => hab.1 e.symm, h1⟩, ?_, hbt.1 h3⟩
      intro d hd
      rcases hd with rfl | hd'
      · exact fun c => hab.2 (G.conflict_symm _ _ c)
      · exact h2 d hd'
    · rintro ⟨⟨-, h1⟩, h2, h3⟩
      exact ⟨h1, fun d hd => h2 d (Or.inr hd), hbt.2 h3⟩

/-- The swap condition for at-start conditions: if `a` is enabled and `b` is enabled after `a`
begins, then `b` is enabled and `a` is enabled after `b` begins. -/
def SwapCond : Prop :=
  ∀ a b, G.Indep a b → ∀ t, G.en a t → G.en b (G.acq a t) → G.en b t ∧ G.en a (G.acq b t)

theorem toDAS_J_BB_iff : G.toDAS.J_BB ↔ G.SwapCond := by
  constructor
  · intro h a b hab t hat hbt
    have hc : G.toDAS.Coherent (t, ∅) := ⟨by simp, by simp⟩
    have hr : G.toDAS.Runs (t, ∅) [Ev.B a, Ev.B b] (G.acq b (G.acq a t), {b, a}) := by
      refine ⟨_, ⟨(G.toDAS_enB a t ∅).2 ⟨by simp, by simp, hat⟩, rfl⟩, _,
        ⟨(G.toDAS_enB b _ _).2 ⟨by simp [hab.1.symm], ?_, hbt⟩, rfl⟩, ?_⟩
      · intro d hd; simp at hd; subst hd; exact fun c => hab.2 (G.conflict_symm _ _ c)
      · rfl
    obtain ⟨c1, ⟨hb0, rfl⟩, c2, ⟨ha1, -⟩, -⟩ := h (t, ∅) hc a b _ hab.1 hr
    rw [toDAS_enB] at hb0 ha1
    exact ⟨hb0.2.2, ha1.2.2⟩
  · intro h c hc a b c' hab hr
    obtain ⟨t, F⟩ := c
    obtain ⟨c1, ⟨hena, rfl⟩, c2, ⟨henb, rfl⟩, hfin⟩ := hr
    simp only [DAS.Runs] at hfin
    subst hfin
    rw [toDAS_enB] at hena henb
    simp only [DAS.nextB, Finset.mem_insert, not_or] at henb
    have hind : G.Indep a b := ⟨hab, fun c => henb.2.1 a (Or.inl rfl) (G.conflict_symm _ _ c)⟩
    obtain ⟨hbt, hab'⟩ := h a b hind t hena.2.2 henb.2.2
    refine ⟨G.toDAS.nextB b (t, F), ⟨(G.toDAS_enB b t F).2 ⟨henb.1.2, fun d hd => henb.2.1 d (Or.inr hd), hbt⟩, rfl⟩,
      G.toDAS.nextB a (G.toDAS.nextB b (t, F)), ⟨(G.toDAS_enB a _ _).2 ⟨?_, ?_, hab'⟩, rfl⟩, ?_⟩
    · simp [hab, hena.1]
    · intro d hd
      simp only [Finset.mem_insert] at hd
      rcases hd with rfl | hd'
      · exact hind.2
      · exact hena.2.1 d hd'
    · exact (G.toDAS.nextB_comm hind (t, F)).symm

/-- **Theorem.** For at-start conditions, Janicki-soundness is the swap condition. -/
theorem toDAS_jsound_iff : G.toDAS.JSound ↔ G.SwapCond := by
  rw [DAS.jsound_iff, toDAS_J_BB_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, G.toDAS.j_ee_of_et G.toDAS_ET_EE⟩⟩

/-- Transparency implies the swap condition; the converse fails (`Examples.lean`). -/
theorem transparent_swapCond (hT : G.Transparent) : G.SwapCond := by
  intro a b hab t hat hbt
  have hbt0 := (hT a b hab t hat).2 hbt
  exact ⟨hbt0, (hT b a hab.symm t hbt0).1 hat⟩

/-- **Theorem.** For at-start conditions, homogeneous step conservativity is the
step-conservativity of Part A. -/
theorem toDAS_hsc_iff_conservative : G.toDAS.HSC ↔ G.Conservative := by
  rw [DAS.hsc_iff_et, toDAS_ET_BB_iff, ← transparent_iff_conservative]
  exact ⟨fun h => h.1, fun h => ⟨h, G.toDAS_ET_EE⟩⟩

/-! ## The least conflict extension -/

/-- Two actions are opaque to each other when one beginning changes the other's enabledness. -/
def Opaque (a b : A) : Prop :=
  ∃ t, (G.en a t ∧ ¬ (G.en b t ↔ G.en b (G.acq a t))) ∨ (G.en b t ∧ ¬ (G.en a t ↔ G.en a (G.acq b t)))

theorem opaque_symm {a b : A} (h : G.Opaque a b) : G.Opaque b a := by
  obtain ⟨t, h⟩ := h
  exact ⟨t, h.symm⟩

/-- The same system with a larger symmetric conflict relation. -/
def withConflict (C : A → A → Prop) (hC : ∀ a b, G.conflict a b → C a b)
    (hs : ∀ a b, C a b → C b a) : GAS S A where
  pre := G.pre
  grd := G.grd
  acq := G.acq
  rel := G.rel
  conflict := C
  conflict_symm := hs
  acq_acq := fun a b hne hnc => G.acq_acq a b hne (fun h => hnc (hC a b h))
  rel_rel := fun a b hne hnc => G.rel_rel a b hne (fun h => hnc (hC a b h))
  acq_rel := fun a b hne hnc => G.acq_rel a b hne (fun h => hnc (hC a b h))

/-- The repair: a conflict on every opaque pair. -/
def repair : GAS S A :=
  G.withConflict (fun a b => G.conflict a b ∨ G.Opaque a b) (fun _ _ h => Or.inl h)
    (fun a b h => h.elim (fun h => Or.inl (G.conflict_symm a b h)) (fun h => Or.inr (G.opaque_symm h)))

theorem repair_transparent : G.repair.Transparent := by
  intro a b hab t hat
  by_contra hcon
  exact hab.2 (Or.inr ⟨t, Or.inl ⟨hat, hcon⟩⟩)

/-- **Corollary (repair).** Adding a conflict on every opaque pair makes any system
step-conservative. -/
theorem repair_conservative : G.repair.Conservative :=
  G.repair.transparent_iff_conservative.1 G.repair_transparent

/-- **Corollary (least).** Any conflict extension that is transparent contains every opaque pair
of distinct actions. -/
theorem repair_least (C : A → A → Prop) (hC : ∀ a b, G.conflict a b → C a b)
    (hs : ∀ a b, C a b → C b a) (hT : (G.withConflict C hC hs).Transparent) :
    ∀ a b, a ≠ b → G.Opaque a b → C a b := by
  intro a b hab hop
  by_contra hnc
  obtain ⟨t, h | h⟩ := hop
  · exact h.2 (hT a b ⟨hab, hnc⟩ t h.1)
  · exact h.2 (hT b a ⟨Ne.symm hab, fun c => hnc (hs b a c)⟩ t h.1)

/-! ## The least conflict extension for soundness -/

/-- Two actions violate the swap condition when one order of their beginnings runs and the
other does not. -/
def SwapViolating (a b : A) : Prop :=
  ∃ t, (G.en a t ∧ G.en b (G.acq a t) ∧ ¬ (G.en b t ∧ G.en a (G.acq b t))) ∨
       (G.en b t ∧ G.en a (G.acq b t) ∧ ¬ (G.en a t ∧ G.en b (G.acq a t)))

theorem swapViolating_symm {a b : A} (h : G.SwapViolating a b) : G.SwapViolating b a := by
  obtain ⟨t, h⟩ := h
  exact ⟨t, h.symm⟩

/-- The repair for soundness: a conflict on every swap-violating pair. -/
def swapRepair : GAS S A :=
  G.withConflict (fun a b => G.conflict a b ∨ G.SwapViolating a b) (fun _ _ h => Or.inl h)
    (fun a b h => h.elim (fun h => Or.inl (G.conflict_symm a b h))
      (fun h => Or.inr (G.swapViolating_symm h)))

theorem swapRepair_swapCond : G.swapRepair.SwapCond := by
  intro a b hab t hat hbt
  by_contra hcon
  exact hab.2 (Or.inr ⟨t, Or.inl ⟨hat, hbt, hcon⟩⟩)

/-- **Corollary (repair for soundness).** Adding a conflict on every swap-violating pair makes
any at-start system Janicki-sound. -/
theorem swapRepair_jsound : G.swapRepair.toDAS.JSound :=
  G.swapRepair.toDAS_jsound_iff.2 G.swapRepair_swapCond

/-- **Corollary (least).** Any conflict extension that satisfies the swap condition contains
every swap-violating pair of distinct actions. -/
theorem swapRepair_least (C : A → A → Prop) (hC : ∀ a b, G.conflict a b → C a b)
    (hs : ∀ a b, C a b → C b a) (hS : (G.withConflict C hC hs).SwapCond) :
    ∀ a b, a ≠ b → G.SwapViolating a b → C a b := by
  intro a b hab hv
  by_contra hnc
  obtain ⟨t, h | h⟩ := hv
  · exact h.2.2 (hS a b ⟨hab, hnc⟩ t h.1 h.2.1)
  · exact h.2.2 (hS b a ⟨Ne.symm hab, fun c => hnc (hs b a c)⟩ t h.1 h.2.1)

end GAS
end IntervalAgents
