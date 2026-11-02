import IntervalAgents.Durative.Characterization

/-!
# Temporal gaps and required concurrency

An action has *no temporal gap* (Cushing et al. 2007) when all its conditions can be checked
at the instant its effects take place: either its effects are all at the end and its over-all
and at-end conditions imply its start condition, or its effects are all at the beginning and
its start and over-all conditions imply its at-end condition. If no action has a temporal gap,
every state reachable by a complete interval run is reachable by a sequence of non-overlapping
actions (`SeqReach`): there is no required concurrency.
-/

set_option linter.unusedSectionVars false

namespace IntervalAgents
namespace DAS

open GAS (Ev)

variable {S A : Type} [DecidableEq A] (D : DAS S A)

/-- A single action run to completion with nothing else in flight. -/
def Fires1 (a : A) (s s' : S) : Prop := D.Runs (s, ∅) [Ev.B a, Ev.E a] (s', ∅)

theorem fires1_iff (a : A) (s s' : S) :
    D.Fires1 a s s' ↔ D.start a s ∧ D.over a (D.acq a s) ∧ D.stop a (D.acq a s) ∧
      s' = D.rel a (D.acq a s) := by
  simp only [Fires1, Runs, Fire]
  constructor
  · rintro ⟨c1, ⟨henb, rfl⟩, c2, ⟨hene, rfl⟩, hfin⟩
    obtain ⟨-, -, hst, hov, -⟩ := henb
    obtain ⟨-, hstop, -⟩ := hene
    simp only [nextB, nextE] at hstop hfin
    refine ⟨hst, hov, hstop, ?_⟩
    have := congrArg Prod.fst hfin
    simpa using this
  · rintro ⟨hst, hov, hstop, rfl⟩
    refine ⟨D.nextB a (s, ∅), ⟨⟨by simp, by simp, hst, hov, by simp⟩, rfl⟩,
      D.nextE a (D.nextB a (s, ∅)), ⟨⟨by simp, by simpa [nextB] using hstop, ?_⟩, rfl⟩, ?_⟩
    · intro d hd hda
      simp at hd
      exact absurd hd hda
    · simp [nextB, nextE]

/-- Sequential reachability: by actions that do not overlap. -/
inductive SeqReach : S → S → Prop
  | refl (s : S) : SeqReach s s
  | step {s s₁ s' : S} (a : A) : D.Fires1 a s s₁ → SeqReach s₁ s' → SeqReach s s'

/-- Interval reachability: by complete runs from a state with nothing in flight. -/
def IntReach (s s' : S) : Prop := ∃ w, D.Runs (s, ∅) w (s', ∅)

theorem SeqReach.snoc {D : DAS S A} : ∀ {s t t' : S}, D.SeqReach s t → ∀ (a : A),
    D.Fires1 a t t' → D.SeqReach s t'
  | _, _, t', SeqReach.refl s, a, h => SeqReach.step a h (SeqReach.refl t')
  | _, _, _, SeqReach.step b hb hr, a, h => SeqReach.step b hb (hr.snoc a h)

theorem seqReach_imp_intReach : ∀ {s s' : S}, D.SeqReach s s' → D.IntReach s s'
  | _, _, SeqReach.refl s => ⟨[], rfl⟩
  | _, _, SeqReach.step a h hr => by
    obtain ⟨w, hw⟩ := seqReach_imp_intReach hr
    exact ⟨[Ev.B a, Ev.E a] ++ w, (D.runs_append _ _ _ _).2 ⟨_, h, hw⟩⟩

/-- No action has a temporal gap. -/
def NoGap : Prop :=
  ∀ a, ((∀ t, D.acq a t = t) ∧ ∀ t, D.over a t → D.stop a t → D.start a t) ∨
       ((∀ t, D.rel a t = t) ∧ ∀ t, D.start a t → D.over a (D.acq a t) → D.stop a (D.acq a t))

/-- The rescheduling invariant: along any run from a coherent configuration, the current
state stays sequentially reachable. -/
theorem runs_seqReach (h : D.NoGap) (s : S) :
    ∀ (w : List (Ev A)) (c c' : Config S A), D.Coherent c → D.SeqReach s c.1 →
      D.Runs c w c' → D.SeqReach s c'.1 := by
  intro w
  induction w with
  | nil => intro c c' _ hs hr; simp [Runs] at hr; subst hr; exact hs
  | cons e w ih =>
    intro c c' hc hs hr
    obtain ⟨c1, hf, hrest⟩ := hr
    have hc1 : D.Coherent c1 := D.coherent_fire hc hf
    refine ih c1 c' hc1 ?_ hrest
    obtain ⟨t, F⟩ := c
    cases e with
    | B a =>
      obtain ⟨⟨-, -, hst, hov, -⟩, rfl⟩ := hf
      simp only [nextB]
      rcases h a with ⟨hacq, -⟩ | ⟨hrel, hgap⟩
      · rw [hacq]; exact hs
      · refine hs.snoc a ((D.fires1_iff a t _).2 ⟨hst, hov, hgap t hst hov, ?_⟩)
        rw [hrel]
    | E a =>
      obtain ⟨⟨haF, hstop, -⟩, rfl⟩ := hf
      simp only [nextE]
      rcases h a with ⟨hacq, hgap⟩ | ⟨hrel, -⟩
      · have hov : D.over a t := hc.2 a haF
        refine hs.snoc a ((D.fires1_iff a t _).2 ⟨hgap t hov hstop, ?_, ?_, ?_⟩)
        · rw [hacq]; exact hov
        · rw [hacq]; exact hstop
        · rw [hacq]
      · rw [hrel]; exact hs

/-- **Theorem (no temporal gap, no required concurrency).** If no action has a temporal gap,
interval reachability and sequential reachability coincide. -/
theorem intReach_iff_seqReach (h : D.NoGap) (s s' : S) : D.IntReach s s' ↔ D.SeqReach s s' := by
  constructor
  · rintro ⟨w, hw⟩
    have hc : D.Coherent (s, ∅) := ⟨by simp, by simp⟩
    exact D.runs_seqReach h s w (s, ∅) (s', ∅) hc (SeqReach.refl s) hw
  · exact D.seqReach_imp_intReach

/-! ## Proving that a state is not sequentially reachable -/

/-- An invariant closed under single complete actions excludes every state outside it. -/
theorem seqReach_inv (Inv : S → Prop) {s : S} (h0 : Inv s)
    (hstep : ∀ a t t', Inv t → D.Fires1 a t t' → Inv t') :
    ∀ {s'}, D.SeqReach s s' → Inv s' := by
  intro s' hr
  induction hr with
  | refl => exact h0
  | step a hf _ ih => exact ih (hstep a _ _ h0 hf)

end DAS
end IntervalAgents
