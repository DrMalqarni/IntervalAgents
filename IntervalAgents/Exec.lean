import IntervalAgents.Characterization

/-!
# Executable interval semantics

A computable version of the interval semantics, proved equal to the relational one
(`runs_iff_runB`). Concrete facts about finite systems are then checked by `decide`.
Also: step sequences (`StepReach`) and the committed discipline.
-/

set_option linter.unusedSectionVars false

namespace IntervalAgents
namespace GAS

variable {S A : Type} [DecidableEq A] (G : GAS S A)

section Exec
variable [∀ a s, Decidable (G.en a s)] [∀ a b, Decidable (G.conflict a b)]

/-- One event, computably. -/
def fireB : Config S A → Ev A → Option (Config S A)
  | (s, F), .B a =>
      if a ∉ F ∧ G.en a s ∧ (∀ b ∈ F, ¬ G.conflict a b) then some (G.acq a s, a :: F) else none
  | (s, F), .E a => if a ∈ F then some (G.rel a s, F.erase a) else none

/-- A word, computably. -/
def runB : Config S A → List (Ev A) → Option (Config S A)
  | c, [] => some c
  | c, e :: x => (G.fireB c e).bind (fun c' => runB c' x)

theorem fire_iff_fireB (c : Config S A) (e : Ev A) (c' : Config S A) :
    G.Fire c e c' ↔ G.fireB c e = some c' := by
  obtain ⟨s, F⟩ := c
  cases e with
  | B a =>
    simp only [Fire, fireB]
    split_ifs with h
    · constructor
      · rintro ⟨-, -, -, rfl⟩; rfl
      · intro h'; cases h'; exact ⟨h.1, h.2.1, h.2.2, rfl⟩
    · constructor
      · rintro ⟨h1, h2, h3, -⟩; exact absurd ⟨h1, h2, h3⟩ h
      · intro h'; cases h'
  | E a =>
    simp only [Fire, fireB]
    split_ifs with h
    · constructor
      · rintro ⟨-, rfl⟩; rfl
      · intro h'; cases h'; exact ⟨h, rfl⟩
    · constructor
      · rintro ⟨h1, -⟩; exact absurd h1 h
      · intro h'; cases h'

theorem runs_iff_runB : ∀ (x : List (Ev A)) (c c' : Config S A),
    G.Runs c x c' ↔ G.runB c x = some c' := by
  intro x
  induction x with
  | nil => intro c c'; simp [Runs, runB, eq_comm]
  | cons e x ih =>
    intro c c'
    simp only [Runs, runB]
    constructor
    · rintro ⟨c1, h1, h2⟩
      rw [(G.fire_iff_fireB c e c1).1 h1]
      exact (ih c1 c').1 h2
    · intro h
      cases hf : G.fireB c e with
      | none => rw [hf] at h; cases h
      | some c1 =>
        rw [hf] at h
        exact ⟨c1, (G.fire_iff_fireB c e c1).2 hf, (ih c1 c').2 h⟩

/-- A word is a complete run from `s` reaching `s'`, computably. -/
def completeRunTo (s : S) (x : List (Ev A)) (s' : S) [DecidableEq S] : Bool :=
  G.runB (s, []) x == some (s', [])


/-- All words of length `n` that run from `c`, with their final configurations, built by
trying every event in `evs` and keeping only those that can fire. -/
def explore (evs : List (Ev A)) : Config S A → Nat → List (List (Ev A) × Config S A)
  | c, 0 => [([], c)]
  | c, n + 1 => evs.flatMap (fun e =>
      match G.fireB c e with
      | none => []
      | some c' => (explore evs c' n).map (fun p => (e :: p.1, p.2)))

/-- Completeness of `explore`: every runnable word appears. -/
theorem mem_explore (evs : List (Ev A)) (hevs : ∀ e, e ∈ evs) :
    ∀ (w : List (Ev A)) (c d : Config S A), G.runB c w = some d →
      (w, d) ∈ G.explore evs c w.length := by
  intro w
  induction w with
  | nil => intro c d h; simp [runB] at h; subst h; simp [explore]
  | cons e w ih =>
    intro c d h
    simp only [runB] at h
    cases hf : G.fireB c e with
    | none => rw [hf] at h; cases h
    | some c' =>
      rw [hf] at h
      simp only [List.length_cons, explore, List.mem_flatMap]
      refine ⟨e, hevs e, ?_⟩
      rw [hf]
      exact List.mem_map.2 ⟨(w, d), ih c' d h, rfl⟩

/-- Soundness of `explore`: every listed word runs. -/
theorem explore_sound (evs : List (Ev A)) :
    ∀ (n : Nat) (c : Config S A) (p : List (Ev A) × Config S A),
      p ∈ G.explore evs c n → G.runB c p.1 = some p.2 := by
  intro n
  induction n with
  | zero => intro c p hp; simp [explore] at hp; subst hp; rfl
  | succ n ih =>
    intro c p hp
    simp only [explore, List.mem_flatMap] at hp
    obtain ⟨e, -, he⟩ := hp
    cases hf : G.fireB c e with
    | none => rw [hf] at he; simp at he
    | some c' =>
      rw [hf] at he
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
      simp only [runB, hf, Option.bind_some]
      exact ih c' q hq

end Exec

/-! ## Step sequences -/

/-- `StepReach s s'`: some step sequence leads from `s` to `s'`. -/
inductive StepReach : S → S → Prop
  | refl (s : S) : StepReach s s
  | step {s s₁ s' : S} (U : List A) : G.StepFires U s s₁ → StepReach s₁ s' → StepReach s s'

/-! ## The committed discipline -/

/-- **Corollary.** If every action publishes nothing when it begins (`acq a = id`), the
discipline is acquire-transparent. -/
theorem committed_transparent (hc : ∀ a s, G.acq a s = s) : G.Transparent := by
  intro a b _ t _
  rw [hc]

/-- **Corollary.** The committed discipline is step-conservative, for every system. -/
theorem committed_conservative (hc : ∀ a s, G.acq a s = s) : G.Conservative :=
  (G.transparent_iff_conservative).1 (G.committed_transparent hc)

end GAS
end IntervalAgents
