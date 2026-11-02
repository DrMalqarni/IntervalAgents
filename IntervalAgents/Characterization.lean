import IntervalAgents.Basic

/-!
# The characterisation theorem

`GAS.transparent_iff_conservative`: a visibility discipline is step-conservative if and only
if it is acquire-transparent (Theorem 2 of the paper). As corollaries we obtain that the
committed discipline is always step-conservative (Corollary 2).
-/

set_option linter.unusedSectionVars false

namespace IntervalAgents
namespace GAS

variable {S A : Type} [DecidableEq A] (G : GAS S A)

/-! ## Runs of concatenated words -/

theorem runs_append (x y : List (Ev A)) :
    ∀ (c c'' : Config S A), G.Runs c (x ++ y) c'' ↔ ∃ c', G.Runs c x c' ∧ G.Runs c' y c'' := by
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

/-! ## Independence facts -/

theorem indep_of_pairwise : ∀ {U : List A}, U.Pairwise G.Indep → ∀ {a b : A},
    a ∈ U → b ∈ U → a ≠ b → G.Indep a b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: r, h, a, b, ha, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hab
    · exact h.1 _ hb'
    · exact (h.1 _ ha').symm
    · exact indep_of_pairwise h.2 ha' hb' hab

theorem perm_pairwise_indep {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    l₁.Pairwise G.Indep ↔ l₂.Pairwise G.Indep :=
  List.Perm.pairwise_iff (R := G.Indep) (fun h => h.symm) hp

/-! ## Beginnings -/

/-- Under transparency, all beginnings of a step run, one after the other. -/
theorem begins_run (hT : G.Transparent) :
    ∀ (p : List A) (s : S) (F : List A), p.Nodup → p.Pairwise G.Indep →
      (∀ a ∈ p, G.en a s) → (∀ a ∈ p, a ∉ F) → (∀ a ∈ p, ∀ b ∈ F, ¬ G.conflict a b) →
      G.Runs (s, F) (p.map Ev.B) (G.acqL p s, p.reverse ++ F) := by
  intro p
  induction p with
  | nil => intro s F _ _ _ _ _; simp [Runs, acqL]
  | cons a r ih =>
    intro s F hnd hpw hen hnF hnc
    have hnd' := List.nodup_cons.1 hnd
    have hpw' := List.pairwise_cons.1 hpw
    refine ⟨(G.acq a s, a :: F), ⟨hnF a (by simp), hen a (by simp),
      hnc a (by simp), rfl⟩, ?_⟩
    have key := ih (G.acq a s) (a :: F) hnd'.2 hpw'.2
      (fun c hc => (hT a c (hpw'.1 c hc) s (hen a (by simp))).1 (hen c (by simp [hc])))
      (fun c hc hcF => by
        rcases List.mem_cons.1 hcF with h | h
        · exact hnd'.1 (h ▸ hc)
        · exact hnF c (by simp [hc]) h)
      (fun c hc b hb => by
        rcases List.mem_cons.1 hb with h | h
        · subst h; exact fun hcf => (hpw'.1 c hc).2 (G.conflict_symm _ _ hcf)
        · exact hnc c (by simp [hc]) b h)
    simpa [acqL, List.reverse_cons, List.append_assoc] using key

/-- Under transparency, if the beginnings of a list of actions run, then all of them are
enabled in the initial state, they are pairwise independent, and the result is determined. -/
theorem begins_inv (hT : G.Transparent) :
    ∀ (p : List A) (s : S) (F : List A) (c : Config S A), G.Runs (s, F) (p.map Ev.B) c →
      p.Nodup ∧ p.Pairwise G.Indep ∧ (∀ a ∈ p, G.en a s) ∧ (∀ a ∈ p, a ∉ F) ∧
      (∀ a ∈ p, ∀ b ∈ F, ¬ G.conflict a b) ∧ c = (G.acqL p s, p.reverse ++ F) := by
  intro p
  induction p with
  | nil => intro s F c h; simp [Runs] at h; simp [h, acqL]
  | cons a r ih =>
    intro s F c h
    obtain ⟨c1, ⟨hnF, hen, hnc, rfl⟩, hrest⟩ := h
    obtain ⟨hnd, hpw, henr, hnotin, hnoc, hc⟩ := ih _ _ _ hrest
    have hind : ∀ x ∈ r, G.Indep a x := fun x hx =>
      ⟨fun e => hnotin x hx (by simp [e]),
       fun hcf => hnoc x hx a (by simp) (G.conflict_symm _ _ hcf)⟩
    refine ⟨List.nodup_cons.2 ⟨fun ha => (hind a ha).1 rfl, hnd⟩,
      List.pairwise_cons.2 ⟨hind, hpw⟩, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with h | h
      · exact h ▸ hen
      · exact (hT a x (hind x h) s hen).2 (henr x h)
    · intro x hx hxF
      rcases List.mem_cons.1 hx with h | h
      · exact hnF (h ▸ hxF)
      · exact hnotin x h (by simp [hxF])
    · intro x hx b hb
      rcases List.mem_cons.1 hx with h | h
      · exact h ▸ hnc b hb
      · exact hnoc x h b (by simp [hb])
    · simpa [acqL, List.reverse_cons, List.append_assoc] using hc

/-! ## Ends -/

theorem ends_run :
    ∀ (q : List A) (t : S) (F : List A), q.Perm F → G.Runs (t, F) (q.map Ev.E) (G.relL q t, []) := by
  intro q
  induction q with
  | nil => intro t F h; simp [Runs, relL, (List.nil_perm.1 h)]
  | cons a r ih =>
    intro t F h
    refine ⟨(G.rel a t, F.erase a), ⟨h.subset (by simp), rfl⟩, ?_⟩
    have h' : r.Perm (F.erase a) := by simpa using h.erase a
    simpa [relL] using ih (G.rel a t) (F.erase a) h'

theorem ends_det :
    ∀ (q : List A) (t : S) (F : List A) (c : Config S A), G.Runs (t, F) (q.map Ev.E) c →
      c.1 = G.relL q t := by
  intro q
  induction q with
  | nil => intro t F c h; simp [Runs] at h; simp [h, relL]
  | cons a r ih =>
    intro t F c h
    obtain ⟨c1, ⟨_, rfl⟩, hrest⟩ := h
    simpa [relL] using ih _ _ _ hrest

/-! ## Algebra of effects -/

theorem acqL_perm {p U : List A} (hp : p.Perm U) (hU : U.Pairwise G.Indep) (s : S) :
    G.acqL p s = G.acqL U s := by
  unfold acqL
  refine hp.foldl_eq' ?_ s
  intro x hx y hy z
  by_cases hxy : x = y
  · subst hxy; rfl
  · have h := G.indep_of_pairwise hU (hp.subset hx) (hp.subset hy) hxy
    exact (G.acq_acq y x (Ne.symm hxy) (fun c => h.2 (G.conflict_symm _ _ c)) z)

theorem relL_perm {q U : List A} (hq : q.Perm U) (hU : U.Pairwise G.Indep) (s : S) :
    G.relL q s = G.relL U s := by
  unfold relL
  refine hq.foldl_eq' ?_ s
  intro x hx y hy z
  by_cases hxy : x = y
  · subst hxy; rfl
  · have h := G.indep_of_pairwise hU (hq.subset hx) (hq.subset hy) hxy
    exact (G.rel_rel y x (Ne.symm hxy) (fun c => h.2 (G.conflict_symm _ _ c)) z)

theorem rel_acqL_comm (a : A) :
    ∀ (r : List A) (x : S), (∀ b ∈ r, G.Indep a b) → G.rel a (G.acqL r x) = G.acqL r (G.rel a x) := by
  intro r
  induction r with
  | nil => intro x _; simp [acqL]
  | cons b r ih =>
    intro x h
    have hab := h b (by simp)
    simp only [acqL, List.foldl_cons] at *
    rw [ih _ (fun c hc => h c (by simp [hc]))]
    congr 1
    exact (G.acq_rel b a (fun e => hab.1 e.symm) (fun c => hab.2 (G.conflict_symm _ _ c)) x).symm

theorem relL_acqL_eq_effL :
    ∀ (U : List A) (s : S), U.Pairwise G.Indep → G.relL U (G.acqL U s) = G.effL U s := by
  intro U
  induction U with
  | nil => intro s _; simp [relL, acqL, effL]
  | cons a r ih =>
    intro s h
    have h' := List.pairwise_cons.1 h
    have e1 : G.relL (a :: r) (G.acqL (a :: r) s) = G.relL r (G.rel a (G.acqL r (G.acq a s))) := by
      simp [relL, acqL]
    rw [e1, G.rel_acqL_comm a r _ h'.1, ih _ h'.2]
    simp [effL, eff]

/-! ## The characterisation -/

theorem step_to_all (hT : G.Transparent) {U : List A} {s s' : S} (h : G.StepFires U s s') :
    ∀ p q, p.Perm U → q.Perm U → G.Runs (s, []) (BEword p q) (s', []) := by
  obtain ⟨⟨_, hnd, hpw⟩, hen, rfl⟩ := h
  intro p q hp hq
  have hpnd : p.Nodup := hp.nodup_iff.2 hnd
  have hppw : p.Pairwise G.Indep := (G.perm_pairwise_indep hp).2 hpw
  have hb := G.begins_run hT p s [] hpnd hppw (fun a ha => hen a (hp.subset ha))
    (fun _ _ h => by simp at h) (fun _ _ _ h => by simp at h)
  have he := G.ends_run q (G.acqL p s) p.reverse (by
    simpa using hq.trans (hp.symm.trans (List.reverse_perm p).symm))
  have hfin : G.relL q (G.acqL p s) = G.effL U s := by
    rw [G.relL_perm hq hpw, G.acqL_perm hp hpw, G.relL_acqL_eq_effL U s hpw]
  rw [← hfin]
  exact (G.runs_append _ _ _ _).2 ⟨_, by simpa using hb, he⟩

theorem some_to_step (hT : G.Transparent) {U : List A} {s s' : S} (hne : U ≠ []) (hnd : U.Nodup)
    {p q : List A} (hp : p.Perm U) (hq : q.Perm U) (hr : G.Runs (s, []) (BEword p q) (s', [])) :
    G.StepFires U s s' := by
  obtain ⟨c, hb, he⟩ := (G.runs_append _ _ _ _).1 hr
  obtain ⟨_, hpw, hen, _, _, rfl⟩ := G.begins_inv hT p s [] c hb
  have hUpw : U.Pairwise G.Indep := (G.perm_pairwise_indep hp).1 hpw
  have hs' := G.ends_det q _ _ _ he
  refine ⟨⟨hne, hnd, hUpw⟩, fun a ha => hen a (hp.symm.subset ha), ?_⟩
  simp only at hs'
  rw [hs', G.relL_perm hq hUpw, G.acqL_perm hp hUpw, G.relL_acqL_eq_effL U s hUpw]

/-- **Theorem (characterisation).** A visibility discipline is step-conservative if and only
if it is acquire-transparent. -/
theorem transparent_iff_conservative : G.Transparent ↔ G.Conservative := by
  constructor
  · intro hT U s s' hne hnd
    have h12 := fun h => G.step_to_all hT (U := U) (s := s) (s' := s') h
    have h23 : (∀ p q, p.Perm U → q.Perm U → G.Runs (s, []) (BEword p q) (s', [])) →
        ∃ p q, p.Perm U ∧ q.Perm U ∧ G.Runs (s, []) (BEword p q) (s', []) :=
      fun h => ⟨U, U, List.Perm.refl _, List.Perm.refl _, h U U (List.Perm.refl _) (List.Perm.refl _)⟩
    have h31 : (∃ p q, p.Perm U ∧ q.Perm U ∧ G.Runs (s, []) (BEword p q) (s', [])) →
        G.StepFires U s s' := fun ⟨p, q, hp, hq, hr⟩ => G.some_to_step hT hne hnd hp hq hr
    exact ⟨⟨h12, fun h => h31 (h23 h)⟩, ⟨h23, fun h => h12 (h31 h)⟩⟩
  · intro hC a b hab t hat
    have hne : [a, b] ≠ [] := by simp
    have hnd : [a, b].Nodup := by simp [hab.1]
    constructor
    · intro hbt
      have hstep : G.StepFires [a, b] t (G.effL [a, b] t) :=
        ⟨⟨hne, hnd, by simp [hab]⟩, by
          intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption, rfl⟩
      have hrun := ((hC [a, b] t _ hne hnd).1.1 hstep) [a, b] [a, b]
        (List.Perm.refl _) (List.Perm.refl _)
      obtain ⟨c1, ⟨_, _, _, rfl⟩, c2, ⟨_, hen2, _, _⟩, _⟩ := hrun
      exact hen2
    · intro hbt
      have hba : b ≠ a := fun e => hab.1 e.symm
      have hrun : G.Runs (t, []) (BEword [a, b] [a, b])
          (G.rel b (G.rel a (G.acq b (G.acq a t))), []) := by
        refine ⟨(G.acq a t, [a]), ⟨by simp, hat, by simp, rfl⟩, ?_⟩
        refine ⟨(G.acq b (G.acq a t), [b, a]), ⟨by simp [hba], hbt, ?_, rfl⟩, ?_⟩
        · intro x hx; simp at hx; subst hx
          exact fun c => hab.2 (G.conflict_symm _ _ c)
        refine ⟨(G.rel a (G.acq b (G.acq a t)), [b]), ⟨by simp, by simp [hba]⟩, ?_⟩
        refine ⟨(G.rel b (G.rel a (G.acq b (G.acq a t))), []), ⟨by simp, by simp⟩, ?_⟩
        rfl
      have h3 : ∃ p q, p.Perm [a, b] ∧ q.Perm [a, b] ∧
          G.Runs (t, []) (BEword p q) (G.rel b (G.rel a (G.acq b (G.acq a t))), []) :=
        ⟨[a, b], [a, b], List.Perm.refl _, List.Perm.refl _, hrun⟩
      have hC' := hC [a, b] t (G.rel b (G.rel a (G.acq b (G.acq a t)))) hne hnd
      exact (hC'.1.2 (hC'.2.2 h3)).2.1 b (by simp)

end GAS
end IntervalAgents
