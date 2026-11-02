import IntervalAgents.Durative.Basic

/-!
# The two characterisation theorems of Part B

* `DAS.hsc_iff_et`: homogeneous step conservativity holds iff beginnings are transparent to
  independent beginnings and endings are transparent to other endings.
* `DAS.jsound_iff`: Janicki-soundness holds iff two adjacent beginnings, or two adjacent
  endings, can always be swapped.
* `DAS.hsc_imp_jsound`: the first implies the second.
-/

set_option linter.unusedSectionVars false

namespace IntervalAgents
namespace DAS

open GAS (Ev)

variable {S A : Type} [DecidableEq A] (D : DAS S A)

/-! ## Runs of concatenated words -/

theorem runs_append (x y : List (Ev A)) :
    ∀ (c c'' : Config S A), D.Runs c (x ++ y) c'' ↔ ∃ c', D.Runs c x c' ∧ D.Runs c' y c'' := by
  induction x with
  | nil => intro c c''; simp [Runs]
  | cons e x ih =>
    intro c c''
    simp only [List.cons_append, Runs]
    constructor
    · rintro ⟨c1, h1, h2⟩
      obtain ⟨c2, h3, h4⟩ := (ih c1 c'').1 h2
      exact ⟨c2, ⟨c1, h1, h3⟩, h4⟩
    · rintro ⟨c2, ⟨c1, h1, h3⟩, h4⟩
      exact ⟨c1, h1, (ih c1 c'').2 ⟨c2, h3, h4⟩⟩

/-! ## Coherence is preserved -/

theorem coherent_nextB {c : Config S A} {b : A} (hc : D.Coherent c) (hb : D.enB b c) :
    D.Coherent (D.nextB b c) := by
  obtain ⟨t, F⟩ := c
  obtain ⟨hnot, hnc, _, hob, hoF⟩ := hb
  obtain ⟨hpw, hov⟩ := hc
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    rcases Finset.mem_insert.1 hx with rfl | hx' <;> rcases Finset.mem_insert.1 hy with rfl | hy'
    · exact absurd rfl hxy
    · exact ⟨hxy, hnc y hy'⟩
    · exact ⟨hxy, fun h => hnc x hx' (D.conflict_symm _ _ h)⟩
    · exact hpw x hx' y hy' hxy
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx'
    · exact hob
    · exact hoF x hx'

theorem coherent_nextE {c : Config S A} {b : A} (hc : D.Coherent c) (hb : D.enE b c) :
    D.Coherent (D.nextE b c) := by
  obtain ⟨t, F⟩ := c
  obtain ⟨_, _, hoth⟩ := hb
  obtain ⟨hpw, _⟩ := hc
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    exact hpw x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
  · intro x hx
    exact hoth x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)

theorem coherent_fire {c c' : Config S A} {e : Ev A} (hc : D.Coherent c) (h : D.Fire c e c') :
    D.Coherent c' := by
  cases e with
  | B b => obtain ⟨hb, rfl⟩ := h; exact D.coherent_nextB hc hb
  | E b => obtain ⟨hb, rfl⟩ := h; exact D.coherent_nextE hc hb

theorem coherent_runs : ∀ (x : List (Ev A)) {c c' : Config S A},
    D.Coherent c → D.Runs c x c' → D.Coherent c'
  | [], c, c', hc, h => by simp [Runs] at h; subst h; exact hc
  | e :: x, c, c', hc, ⟨c1, h1, h2⟩ => coherent_runs x (D.coherent_fire hc h1) h2

/-! ## Independence facts and the algebra of effects -/

theorem indep_of_pairwise : ∀ {U : List A}, U.Pairwise D.Indep → ∀ {a b : A},
    a ∈ U → b ∈ U → a ≠ b → D.Indep a b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: r, h, a, b, ha, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hab
    · exact h.1 _ hb'
    · exact (h.1 _ ha').symm
    · exact indep_of_pairwise h.2 ha' hb' hab

theorem perm_pairwise_indep {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    l₁.Pairwise D.Indep ↔ l₂.Pairwise D.Indep :=
  List.Perm.pairwise_iff (R := D.Indep) (fun h => h.symm) hp

theorem acqL_perm {p U : List A} (hp : p.Perm U) (hU : U.Pairwise D.Indep) (s : S) :
    D.acqL p s = D.acqL U s := by
  unfold acqL
  refine hp.foldl_eq' ?_ s
  intro x hx y hy z
  by_cases hxy : x = y
  · subst hxy; rfl
  · have h := D.indep_of_pairwise hU (hp.subset hx) (hp.subset hy) hxy
    exact (D.acq_acq y x (Ne.symm hxy) (fun c => h.2 (D.conflict_symm _ _ c)) z)

theorem relL_perm {q U : List A} (hq : q.Perm U) (hU : U.Pairwise D.Indep) (s : S) :
    D.relL q s = D.relL U s := by
  unfold relL
  refine hq.foldl_eq' ?_ s
  intro x hx y hy z
  by_cases hxy : x = y
  · subst hxy; rfl
  · have h := D.indep_of_pairwise hU (hq.subset hx) (hq.subset hy) hxy
    exact (D.rel_rel y x (Ne.symm hxy) (fun c => h.2 (D.conflict_symm _ _ c)) z)

/-- The in-flight set after a beginning step does not depend on the order. -/
theorem insert_union_toFinset (a : A) (r : List A) (F : Finset A) :
    insert a F ∪ r.toFinset = F ∪ (a :: r).toFinset := by
  ext x; simp [or_left_comm, or_assoc]

theorem erase_sdiff_toFinset (a : A) (r : List A) (F : Finset A) :
    F.erase a \ r.toFinset = F \ (a :: r).toFinset := by
  ext x; simp [Finset.mem_sdiff, Finset.mem_erase]; tauto

/-! ## Beginnings under ET_BB -/

/-- Under the forward half of ET_BB, all beginnings of a step run, one after the other. -/
theorem begins_run (hT : D.ET_BB_fwd) :
    ∀ (p : List A) (c : Config S A), D.Coherent c → p.Nodup → p.Pairwise D.Indep →
      (∀ b ∈ p, D.enB b c) → D.Runs c (p.map Ev.B) (D.acqL p c.1, c.2 ∪ p.toFinset) := by
  intro p
  induction p with
  | nil => intro c _ _ _ _; obtain ⟨t, F⟩ := c; simp [Runs, acqL]
  | cons a r ih =>
    intro c hc hnd hpw hen
    obtain ⟨t, F⟩ := c
    have hnd' := List.nodup_cons.1 hnd
    have hpw' := List.pairwise_cons.1 hpw
    have hena : D.enB a (t, F) := hen a (by simp)
    refine ⟨D.nextB a (t, F), ⟨hena, rfl⟩, ?_⟩
    have hc1 : D.Coherent (D.nextB a (t, F)) := D.coherent_nextB hc hena
    have hen1 : ∀ b ∈ r, D.enB b (D.nextB a (t, F)) := fun b hb =>
      hT (t, F) hc a b (hpw'.1 b hb) hena (hen b (by simp [hb]))
    have key := ih (D.nextB a (t, F)) hc1 hnd'.2 hpw'.2 hen1
    simp only [nextB] at key ⊢
    rw [insert_union_toFinset] at key
    simpa [acqL] using key

/-- Under the backward half of ET_BB, if the beginnings of a list run from a coherent
configuration, the list is a step enabled there and the result is determined. -/
theorem begins_inv (hT : D.ET_BB_bwd) :
    ∀ (p : List A) (c c' : Config S A), D.Coherent c → D.Runs c (p.map Ev.B) c' →
      p.Nodup ∧ p.Pairwise D.Indep ∧ (∀ b ∈ p, D.enB b c) ∧ c' = (D.acqL p c.1, c.2 ∪ p.toFinset) := by
  intro p
  induction p with
  | nil => intro c c' _ h; obtain ⟨t, F⟩ := c; simp [Runs] at h; simp [h, acqL]
  | cons a r ih =>
    intro c c' hc h
    obtain ⟨t, F⟩ := c
    obtain ⟨c1, ⟨hena, rfl⟩, hrest⟩ := h
    have hc1 : D.Coherent (D.nextB a (t, F)) := D.coherent_nextB hc hena
    obtain ⟨hnd, hpw, henr, hc'⟩ := ih _ _ hc1 hrest
    have hind : ∀ b ∈ r, D.Indep a b := fun b hb => by
      obtain ⟨hnot, hnc, -, -, -⟩ := henr b hb
      simp only [Finset.mem_insert, not_or] at hnot hnc
      exact ⟨fun e => hnot.1 e.symm, fun h => hnc a (by simp) (D.conflict_symm _ _ h)⟩
    refine ⟨List.nodup_cons.2 ⟨fun ha => (hind a ha).1 rfl, hnd⟩,
      List.pairwise_cons.2 ⟨hind, hpw⟩, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact hena
      · exact hT (t, F) hc a b (hind b hb') hena (henr b hb')
    · rw [hc']
      simp only [nextB]
      rw [insert_union_toFinset]
      simp [acqL]

/-! ## Endings under ET_EE -/

theorem ends_run (hT : D.ET_EE_fwd) :
    ∀ (p : List A) (c : Config S A), D.Coherent c → p.Nodup →
      (∀ b ∈ p, D.enE b c) → D.Runs c (p.map Ev.E) (D.relL p c.1, c.2 \ p.toFinset) := by
  intro p
  induction p with
  | nil => intro c _ _ _; obtain ⟨t, F⟩ := c; simp [Runs, relL]
  | cons a r ih =>
    intro c hc hnd hen
    obtain ⟨t, F⟩ := c
    have hnd' := List.nodup_cons.1 hnd
    have hena : D.enE a (t, F) := hen a (by simp)
    refine ⟨D.nextE a (t, F), ⟨hena, rfl⟩, ?_⟩
    have hc1 : D.Coherent (D.nextE a (t, F)) := D.coherent_nextE hc hena
    have hen1 : ∀ b ∈ r, D.enE b (D.nextE a (t, F)) := fun b hb =>
      hT (t, F) hc a b (fun e => hnd'.1 (e ▸ hb)) hena (hen b (by simp [hb]))
    have key := ih (D.nextE a (t, F)) hc1 hnd'.2 hen1
    simp only [nextE] at key ⊢
    rw [erase_sdiff_toFinset] at key
    simpa [relL] using key

theorem ends_inv (hT : D.ET_EE_bwd) :
    ∀ (p : List A) (c c' : Config S A), D.Coherent c → D.Runs c (p.map Ev.E) c' →
      p.Nodup ∧ p.Pairwise D.Indep ∧ (∀ b ∈ p, D.enE b c) ∧ c' = (D.relL p c.1, c.2 \ p.toFinset) := by
  intro p
  induction p with
  | nil => intro c c' _ h; obtain ⟨t, F⟩ := c; simp [Runs] at h; simp [h, relL]
  | cons a r ih =>
    intro c c' hc h
    obtain ⟨t, F⟩ := c
    obtain ⟨c1, ⟨hena, rfl⟩, hrest⟩ := h
    have hc1 : D.Coherent (D.nextE a (t, F)) := D.coherent_nextE hc hena
    obtain ⟨hnd, hpw, henr, hc'⟩ := ih _ _ hc1 hrest
    have hne : ∀ b ∈ r, b ≠ a := fun b hb => by
      obtain ⟨hmem, -, -⟩ := henr b hb
      exact Finset.ne_of_mem_erase hmem
    have hind : ∀ b ∈ r, D.Indep a b := fun b hb => by
      obtain ⟨hmem, -, -⟩ := henr b hb
      exact hc.1 a hena.1 b (Finset.mem_of_mem_erase hmem) (fun e => hne b hb e.symm)
    refine ⟨List.nodup_cons.2 ⟨fun ha => hne a ha rfl, hnd⟩,
      List.pairwise_cons.2 ⟨hind, hpw⟩, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact hena
      · exact hT (t, F) hc a b (fun e => hne b hb' e.symm) hena (henr b hb')
    · rw [hc']
      simp only [nextE]
      rw [erase_sdiff_toFinset]
      simp [relL]

/-! ## The first characterisation -/

theorem nextB_nextB_eq (a b : A) (t : S) (F : Finset A) :
    D.nextB b (D.nextB a (t, F)) = (D.acqL [a, b] t, F ∪ [a, b].toFinset) := by
  simp only [nextB, acqL, List.foldl_cons, List.foldl_nil]
  congr 1
  ext x; simp; tauto

theorem nextE_nextE_eq (a b : A) (t : S) (F : Finset A) :
    D.nextE b (D.nextE a (t, F)) = (D.relL [a, b] t, F \ [a, b].toFinset) := by
  simp only [nextE, relL, List.foldl_cons, List.foldl_nil]
  congr 1
  ext x; simp [Finset.mem_sdiff, Finset.mem_erase]; tauto

/-- Two-action necessity, forward halves: if every enabled homogeneous step runs in every
order, then no beginning disables an independent beginning and no ending disables another
ending. -/
theorem et_fwd_of_hsc_fwd (h : D.HSC_fwd) : D.ET_BB_fwd ∧ D.ET_EE_fwd := by
  constructor
  · intro c hc a b hab hena henb
    obtain ⟨t, F⟩ := c
    have hstep : D.BStep [a, b] (t, F) (D.acqL [a, b] t, F ∪ [a, b].toFinset) :=
      ⟨by simp, by simp [hab.1], by simp [hab], by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption, rfl⟩
    obtain ⟨c1, ⟨-, rfl⟩, c2, ⟨hen2, -⟩, -⟩ := ((h (t, F) hc [a, b] _).1 hstep) [a, b] (List.Perm.refl _)
    exact hen2
  · intro c hc a b hab hena henb
    obtain ⟨t, F⟩ := c
    have hind : D.Indep a b := hc.1 a hena.1 b henb.1 hab
    have hstep : D.EStep [a, b] (t, F) (D.relL [a, b] t, F \ [a, b].toFinset) :=
      ⟨by simp, by simp [hab], by simp [hind], by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption, rfl⟩
    obtain ⟨c1, ⟨-, rfl⟩, c2, ⟨hen2, -⟩, -⟩ := ((h (t, F) hc [a, b] _).2 hstep) [a, b] (List.Perm.refl _)
    exact hen2

/-- Two-action necessity, backward halves: if every run of a homogeneous word is an enabled
step, then no beginning enables an independent beginning and no ending enables another ending. -/
theorem et_bwd_of_hsc_bwd (h : D.HSC_bwd) : D.ET_BB_bwd ∧ D.ET_EE_bwd := by
  constructor
  · intro c hc a b hab hena henb'
    obtain ⟨t, F⟩ := c
    have hrun : D.Runs (t, F) ([a, b].map Ev.B) (D.acqL [a, b] t, F ∪ [a, b].toFinset) := by
      refine ⟨D.nextB a (t, F), ⟨hena, rfl⟩, D.nextB b (D.nextB a (t, F)), ⟨henb', rfl⟩, ?_⟩
      exact (D.nextB_nextB_eq a b t F).symm
    exact ((h (t, F) hc [a, b] _ (by simp) (by simp [hab.1])).1
      ⟨[a, b], List.Perm.refl _, hrun⟩).2.2.2.1 b (by simp)
  · intro c hc a b hab hena henb'
    obtain ⟨t, F⟩ := c
    have hrun : D.Runs (t, F) ([a, b].map Ev.E) (D.relL [a, b] t, F \ [a, b].toFinset) := by
      refine ⟨D.nextE a (t, F), ⟨hena, rfl⟩, D.nextE b (D.nextE a (t, F)), ⟨henb', rfl⟩, ?_⟩
      exact (D.nextE_nextE_eq a b t F).symm
    exact ((h (t, F) hc [a, b] _ (by simp) (by simp [hab])).2
      ⟨[a, b], List.Perm.refl _, hrun⟩).2.2.2.1 b (by simp)

/-- Sufficiency, forward halves. -/
theorem hsc_fwd_of_et_fwd (hBB : D.ET_BB_fwd) (hEE : D.ET_EE_fwd) : D.HSC_fwd := by
  intro c hc X c'
  obtain ⟨t, F⟩ := c
  constructor
  · rintro ⟨-, hnd, hpw, hen, rfl⟩ p hp
    have hpnd : p.Nodup := hp.nodup_iff.2 hnd
    have hppw : p.Pairwise D.Indep := (D.perm_pairwise_indep hp).2 hpw
    have hr := D.begins_run hBB p (t, F) hc hpnd hppw (fun b hb => hen b (hp.subset hb))
    rwa [D.acqL_perm hp hpw, List.toFinset_eq_of_perm _ _ hp] at hr
  · rintro ⟨-, hnd, hpw, hen, rfl⟩ p hp
    have hpnd : p.Nodup := hp.nodup_iff.2 hnd
    have hr := D.ends_run hEE p (t, F) hc hpnd (fun b hb => hen b (hp.subset hb))
    rwa [D.relL_perm hp hpw, List.toFinset_eq_of_perm _ _ hp] at hr

/-- Sufficiency, backward halves. -/
theorem hsc_bwd_of_et_bwd (hBB : D.ET_BB_bwd) (hEE : D.ET_EE_bwd) : D.HSC_bwd := by
  intro c hc X c' hne hnd
  obtain ⟨t, F⟩ := c
  constructor
  · rintro ⟨p, hp, hr⟩
    obtain ⟨-, hppw, hen, rfl⟩ := D.begins_inv hBB p (t, F) c' hc hr
    have hXpw : X.Pairwise D.Indep := (D.perm_pairwise_indep hp).1 hppw
    refine ⟨hne, hnd, hXpw, fun b hb => hen b (hp.symm.subset hb), ?_⟩
    rw [D.acqL_perm hp hXpw, List.toFinset_eq_of_perm _ _ hp]
  · rintro ⟨p, hp, hr⟩
    obtain ⟨-, hppw, hen, rfl⟩ := D.ends_inv hEE p (t, F) c' hc hr
    have hXpw : X.Pairwise D.Indep := (D.perm_pairwise_indep hp).1 hppw
    refine ⟨hne, hnd, hXpw, fun b hb => hen b (hp.symm.subset hb), ?_⟩
    rw [D.relL_perm hp hXpw, List.toFinset_eq_of_perm _ _ hp]

/-- **Theorem (forward half).** Every enabled homogeneous step runs in every order iff no
beginning disables an independent beginning and no ending disables another ending. -/
theorem hsc_fwd_iff : D.HSC_fwd ↔ D.ET_BB_fwd ∧ D.ET_EE_fwd :=
  ⟨D.et_fwd_of_hsc_fwd, fun h => D.hsc_fwd_of_et_fwd h.1 h.2⟩

/-- **Theorem (backward half).** Every run of a homogeneous word is an enabled step iff no
beginning enables an independent beginning and no ending enables another ending. -/
theorem hsc_bwd_iff : D.HSC_bwd ↔ D.ET_BB_bwd ∧ D.ET_EE_bwd :=
  ⟨D.et_bwd_of_hsc_bwd, fun h => D.hsc_bwd_of_et_bwd h.1 h.2⟩

/-- Conservativity is the conjunction of its two halves. -/
theorem hsc_iff_halves : D.HSC ↔ D.HSC_fwd ∧ D.HSC_bwd := by
  constructor
  · intro h
    refine ⟨fun c hc X c' => ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩, fun c hc X c' hne hnd => ⟨?_, ?_⟩⟩
    · obtain ⟨t, F⟩ := c
      have hne : X ≠ [] := hs.1
      have hnd : X.Nodup := hs.2.1
      exact ((h (t, F) hc X c' hne hnd).1.1.1 hs) p hp
    · obtain ⟨t, F⟩ := c
      have hne : X ≠ [] := hs.1
      have hnd : X.Nodup := hs.2.1
      exact ((h (t, F) hc X c' hne hnd).2.1.1 hs) p hp
    · intro hsome
      exact (h c hc X c' hne hnd).1.1.2 ((h c hc X c' hne hnd).1.2.2 hsome)
    · intro hsome
      exact (h c hc X c' hne hnd).2.1.2 ((h c hc X c' hne hnd).2.2.2 hsome)
  · rintro ⟨hf, hb⟩ c hc X c' hne hnd
    refine ⟨⟨⟨(hf c hc X c').1, fun hall => (hb c hc X c' hne hnd).1 ⟨X, List.Perm.refl _, hall X (List.Perm.refl _)⟩⟩,
      ⟨fun hall => ⟨X, List.Perm.refl _, hall X (List.Perm.refl _)⟩,
       fun hsome => (hf c hc X c').1 ((hb c hc X c' hne hnd).1 hsome)⟩⟩,
      ⟨⟨(hf c hc X c').2, fun hall => (hb c hc X c' hne hnd).2 ⟨X, List.Perm.refl _, hall X (List.Perm.refl _)⟩⟩,
       ⟨fun hall => ⟨X, List.Perm.refl _, hall X (List.Perm.refl _)⟩,
        fun hsome => (hf c hc X c').2 ((hb c hc X c' hne hnd).2 hsome)⟩⟩⟩

theorem et_of_hsc (h : D.HSC) : D.ET_BB ∧ D.ET_EE := by
  obtain ⟨hf, hb⟩ := D.hsc_iff_halves.1 h
  obtain ⟨f1, f2⟩ := D.et_fwd_of_hsc_fwd hf
  obtain ⟨b1, b2⟩ := D.et_bwd_of_hsc_bwd hb
  exact ⟨D.ET_BB_iff.2 ⟨f1, b1⟩, D.ET_EE_iff.2 ⟨f2, b2⟩⟩

theorem hsc_of_et (hBB : D.ET_BB) (hEE : D.ET_EE) : D.HSC := by
  obtain ⟨f1, b1⟩ := D.ET_BB_iff.1 hBB
  obtain ⟨f2, b2⟩ := D.ET_EE_iff.1 hEE
  exact D.hsc_iff_halves.2 ⟨D.hsc_fwd_of_et_fwd f1 f2, D.hsc_bwd_of_et_bwd b1 b2⟩

/-- **Theorem (Part B, consistency).** Homogeneous step conservativity holds if and only if
beginnings are transparent to independent beginnings and endings to other endings. -/
theorem hsc_iff_et : D.HSC ↔ D.ET_BB ∧ D.ET_EE :=
  ⟨D.et_of_hsc, fun h => D.hsc_of_et h.1 h.2⟩

/-! ## The second characterisation -/

theorem jsound_iff : D.JSound ↔ D.J_BB ∧ D.J_EE := by
  constructor
  · intro h
    refine ⟨fun c hc a b c' hab hr => ?_, fun c hc a b c' hab hr => ?_⟩
    · simpa using h c hc [] [] (Ev.B a) (Ev.B b) c' hab (by simpa using hr)
    · simpa using h c hc [] [] (Ev.E a) (Ev.E b) c' hab (by simpa using hr)
  · rintro ⟨hBB, hEE⟩ c hc x y e f c' hef hr
    obtain ⟨c1, hx, hrest⟩ := (D.runs_append x _ c c').1 hr
    have hc1 : D.Coherent c1 := D.coherent_runs x hc hx
    have hrest' : D.Runs c1 ([e, f] ++ y) c' := by simpa using hrest
    obtain ⟨c2, h2, hy⟩ := (D.runs_append [e, f] y c1 c').1 hrest'
    have hsw : D.Runs c1 [f, e] c2 := by
      cases e with
      | B a => cases f with
        | B b => exact hBB c1 hc1 a b c2 hef h2
        | E b => exact absurd hef (by simp [SameKind])
      | E a => cases f with
        | B b => exact absurd hef (by simp [SameKind])
        | E b => exact hEE c1 hc1 a b c2 hef h2
    refine (D.runs_append x _ c c').2 ⟨c1, hx, ?_⟩
    have : D.Runs c1 ([f, e] ++ y) c' := (D.runs_append [f, e] y c1 c').2 ⟨c2, hsw, hy⟩
    simpa using this

theorem nextB_comm {a b : A} (hab : D.Indep a b) (c : Config S A) :
    D.nextB a (D.nextB b c) = D.nextB b (D.nextB a c) := by
  obtain ⟨t, F⟩ := c
  simp only [nextB]
  rw [D.acq_acq a b hab.1 hab.2, Finset.insert_comm]

theorem nextE_comm {a b : A} (hab : D.Indep a b) (c : Config S A) :
    D.nextE a (D.nextE b c) = D.nextE b (D.nextE a c) := by
  obtain ⟨t, F⟩ := c
  simp only [nextE]
  rw [D.rel_rel a b hab.1 hab.2, Finset.erase_right_comm]

theorem j_bb_of_et (hT : D.ET_BB) : D.J_BB := by
  intro c hc a b c' hab hr
  obtain ⟨c1, ⟨hena, rfl⟩, c2, ⟨henb, rfl⟩, hfin⟩ := hr
  simp only [Runs] at hfin
  subst hfin
  have hind : D.Indep a b := by
    obtain ⟨t, F⟩ := c
    obtain ⟨hnot, hnc, -, -, -⟩ := henb
    simp only [Finset.mem_insert, not_or] at hnot hnc
    exact ⟨fun e => hnot.1 e.symm, fun h => hnc a (by simp) (D.conflict_symm _ _ h)⟩
  have henb0 : D.enB b c := (hT c hc a b hind hena).2 henb
  have hena' : D.enB a (D.nextB b c) := (hT c hc b a hind.symm henb0).1 hena
  refine ⟨D.nextB b c, ⟨henb0, rfl⟩, D.nextB a (D.nextB b c), ⟨hena', rfl⟩, ?_⟩
  simp only [Runs]
  exact (D.nextB_comm hind c).symm

theorem j_ee_of_et (hT : D.ET_EE) : D.J_EE := by
  intro c hc a b c' hab hr
  obtain ⟨c1, ⟨hena, rfl⟩, c2, ⟨henb, rfl⟩, hfin⟩ := hr
  simp only [Runs] at hfin
  subst hfin
  have hind : D.Indep a b := by
    obtain ⟨t, F⟩ := c
    exact hc.1 a hena.1 b (Finset.mem_of_mem_erase henb.1) hab
  have henb0 : D.enE b c := (hT c hc a b hab hena).2 henb
  have hena' : D.enE a (D.nextE b c) := (hT c hc b a (Ne.symm hab) henb0).1 hena
  refine ⟨D.nextE b c, ⟨henb0, rfl⟩, D.nextE a (D.nextE b c), ⟨hena', rfl⟩, ?_⟩
  simp only [Runs]
  exact (D.nextE_comm hind c).symm

/-- **Corollary.** Homogeneous step conservativity implies Janicki-soundness. -/
theorem hsc_imp_jsound (h : D.HSC) : D.JSound := by
  obtain ⟨hBB, hEE⟩ := D.et_of_hsc h
  exact D.jsound_iff.2 ⟨D.j_bb_of_et hBB, D.j_ee_of_et hEE⟩

theorem not_jsound_of_not_J_BB (h : ¬ D.J_BB) : ¬ D.JSound := fun hs => h (D.jsound_iff.1 hs).1
theorem not_jsound_of_not_J_EE (h : ¬ D.J_EE) : ¬ D.JSound := fun hs => h (D.jsound_iff.1 hs).2
theorem not_hsc_of_not_ET_BB (h : ¬ D.ET_BB) : ¬ D.HSC := fun hs => h (D.et_of_hsc hs).1
theorem not_hsc_of_not_ET_EE (h : ¬ D.ET_EE) : ¬ D.HSC := fun hs => h (D.et_of_hsc hs).2

end DAS
end IntervalAgents
