import Mathlib.Data.List.Perm.Basic

/-!
# Guarded action systems and their interval semantics

A guarded action system with a visibility discipline. Following the paper, every action `a`
has a precondition `pre a`, a guard `grd a`, and an effect split into the part `acq a`
applied when `a` begins and the part `rel a` applied when it ends, so that the effect is
`eff a = rel a ∘ acq a`. The committed discipline is the special case `acq a = id`.

Assumptions (all stated as fields, so every theorem makes them explicit):
* `conflict` is symmetric;
* for independent actions (`a ≠ b` and not in conflict) every piece of `a` (`acq a`, `rel a`)
  commutes with every piece of `b`.
-/

namespace IntervalAgents

/-- A guarded action system together with a visibility discipline. -/
structure GAS (S A : Type) where
  pre : A → S → Prop
  grd : A → S → Prop
  acq : A → S → S
  rel : A → S → S
  conflict : A → A → Prop
  conflict_symm : ∀ a b, conflict a b → conflict b a
  acq_acq : ∀ a b, a ≠ b → ¬ conflict a b → ∀ s, acq a (acq b s) = acq b (acq a s)
  rel_rel : ∀ a b, a ≠ b → ¬ conflict a b → ∀ s, rel a (rel b s) = rel b (rel a s)
  acq_rel : ∀ a b, a ≠ b → ¬ conflict a b → ∀ s, acq a (rel b s) = rel b (acq a s)

variable {S A : Type}

namespace GAS

variable (G : GAS S A)

/-- An action is enabled when its precondition and its guard hold. -/
def en (a : A) (s : S) : Prop := G.pre a s ∧ G.grd a s

/-- The effect of an action. -/
def eff (a : A) (s : S) : S := G.rel a (G.acq a s)

/-- Two actions are independent if they are distinct and not in conflict. -/
def Indep (a b : A) : Prop := a ≠ b ∧ ¬ G.conflict a b

theorem Indep.symm {G : GAS S A} {a b : A} (h : G.Indep a b) : G.Indep b a :=
  ⟨fun e => h.1 e.symm, fun c => h.2 (G.conflict_symm _ _ c)⟩

/-- Apply the effects of a list of actions, first element first. -/
def effL (l : List A) (s : S) : S := l.foldl (fun t a => G.eff a t) s
/-- Apply the acquire parts of a list of actions. -/
def acqL (l : List A) (s : S) : S := l.foldl (fun t a => G.acq a t) s
/-- Apply the release parts of a list of actions. -/
def relL (l : List A) (s : S) : S := l.foldl (fun t a => G.rel a t) s

/-! ## Step semantics -/

/-- A step: a duplicate-free list of pairwise independent actions. -/
def IsStep (U : List A) : Prop := U ≠ [] ∧ U.Nodup ∧ U.Pairwise G.Indep

/-- `StepFires U s s'`: the step `U` fires from `s` to `s'` (guards read a priori, in `s`). -/
def StepFires (U : List A) (s s' : S) : Prop :=
  G.IsStep U ∧ (∀ a ∈ U, G.en a s) ∧ s' = G.effL U s

/-! ## Interval semantics -/

variable [DecidableEq A]

/-- Beginnings and ends of actions. -/
inductive Ev (A : Type) where
  | B : A → Ev A
  | E : A → Ev A
  deriving DecidableEq

/-- Configurations: a state and the list of actions in flight. -/
abbrev Config (S A : Type) := S × List A

/-- One event of the interval semantics. -/
def Fire : Config S A → Ev A → Config S A → Prop
  | (s, F), .B a, c' => a ∉ F ∧ G.en a s ∧ (∀ b ∈ F, ¬ G.conflict a b) ∧ c' = (G.acq a s, a :: F)
  | (s, F), .E a, c' => a ∈ F ∧ c' = (G.rel a s, F.erase a)

/-- A word of events runs from one configuration to another. -/
def Runs : Config S A → List (Ev A) → Config S A → Prop
  | c, [], c' => c' = c
  | c, e :: x, c'' => ∃ c', G.Fire c e c' ∧ Runs c' x c''

/-- The interval words of a step `U`: all beginnings (in the order `p`) before all ends
(in the order `q`), where `p` and `q` enumerate `U`. -/
def BEword (p q : List A) : List (Ev A) := p.map Ev.B ++ q.map Ev.E

/-! ## The two properties related by the main theorem -/

/-- Acquire-transparency: beginning an action never changes whether an independent
action is enabled. -/
def Transparent : Prop :=
  ∀ a b, G.Indep a b → ∀ t, G.en a t → (G.en b t ↔ G.en b (G.acq a t))

/-- Step-conservativity: for every state and every duplicate-free nonempty list `U`,
(1) the step fires, (2) every interval word of `U` runs, (3) some interval word of `U` runs,
are equivalent. -/
def Conservative : Prop :=
  ∀ (U : List A) (s s' : S), U ≠ [] → U.Nodup →
    (G.StepFires U s s' ↔
        ∀ p q, p.Perm U → q.Perm U → G.Runs (s, []) (BEword p q) (s', [])) ∧
    ((∀ p q, p.Perm U → q.Perm U → G.Runs (s, []) (BEword p q) (s', [])) ↔
        ∃ p q, p.Perm U ∧ q.Perm U ∧ G.Runs (s, []) (BEword p q) (s', []))

end GAS
end IntervalAgents
