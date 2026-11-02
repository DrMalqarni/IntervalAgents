import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Perm.Basic
import IntervalAgents.Basic

/-!
# Durative action systems: three condition sets and configurations

Part B of the paper. An action `a` now carries three conditions:
* `start a`, checked in the state in which `a` begins;
* `over a`, required in every state from the one just after `a` begins up to and including
  the one in which `a` ends (the over-all condition);
* `stop a`, required in the state in which `a` ends (the at-end condition; `end` is reserved).

Effects are split as before: `acq a` at the beginning, `rel a` at the end.

Runs start from *configurations*: a state together with the finite set of actions in flight.
A configuration is *coherent* when the actions in flight are pairwise independent and every
one of their over-all conditions holds. Every marking of the double-arc net or of a split net
is such a configuration, and the semantics is defined from any of them.

The semantics is the blocking one: an event is enabled only if it does not falsify the
over-all condition of any action in flight (including, for a beginning, the action's own).
A run generated without these checks is *valid* exactly when it is a run in this sense, so
the blocking and the validation reading of over-all conditions define the same runs.
-/

namespace IntervalAgents

/-- A durative action system with a visibility discipline. -/
structure DAS (S A : Type) where
  start : A → S → Prop
  over : A → S → Prop
  stop : A → S → Prop
  acq : A → S → S
  rel : A → S → S
  conflict : A → A → Prop
  conflict_symm : ∀ a b, conflict a b → conflict b a
  acq_acq : ∀ a b, a ≠ b → ¬ conflict a b → ∀ s, acq a (acq b s) = acq b (acq a s)
  rel_rel : ∀ a b, a ≠ b → ¬ conflict a b → ∀ s, rel a (rel b s) = rel b (rel a s)
  acq_rel : ∀ a b, a ≠ b → ¬ conflict a b → ∀ s, acq a (rel b s) = rel b (acq a s)

variable {S A : Type}

namespace DAS

variable (D : DAS S A)

/-- Two actions are independent if they are distinct and not in conflict. -/
def Indep (a b : A) : Prop := a ≠ b ∧ ¬ D.conflict a b

theorem Indep.symm {D : DAS S A} {a b : A} (h : D.Indep a b) : D.Indep b a :=
  ⟨fun e => h.1 e.symm, fun c => h.2 (D.conflict_symm _ _ c)⟩

/-- The effect of a complete action. -/
def eff (a : A) (s : S) : S := D.rel a (D.acq a s)

def acqL (l : List A) (s : S) : S := l.foldl (fun t a => D.acq a t) s
def relL (l : List A) (s : S) : S := l.foldl (fun t a => D.rel a t) s

variable [DecidableEq A]

/-- Configurations: a state and the finite set of actions in flight. -/
abbrev Config (S A : Type) := S × Finset A

/-- A configuration is coherent when the actions in flight are pairwise independent and all
their over-all conditions hold. -/
def Coherent : Config S A → Prop
  | (t, F) => (∀ a ∈ F, ∀ b ∈ F, a ≠ b → D.Indep a b) ∧ ∀ a ∈ F, D.over a t

/-! ## Events -/

/-- The beginning of `b` is enabled: `b` is not in flight, conflicts with nothing in flight,
its start condition holds, and after its acquire part its own over-all condition and those of
all actions in flight hold. -/
def enB (b : A) : Config S A → Prop
  | (t, F) => b ∉ F ∧ (∀ d ∈ F, ¬ D.conflict b d) ∧ D.start b t ∧ D.over b (D.acq b t) ∧
      ∀ d ∈ F, D.over d (D.acq b t)

/-- The ending of `b` is enabled: `b` is in flight, its at-end condition holds, and after its
release part the over-all conditions of the other actions in flight hold. -/
def enE (b : A) : Config S A → Prop
  | (t, F) => b ∈ F ∧ D.stop b t ∧ ∀ d ∈ F, d ≠ b → D.over d (D.rel b t)

def nextB (b : A) : Config S A → Config S A
  | (t, F) => (D.acq b t, insert b F)

def nextE (b : A) : Config S A → Config S A
  | (t, F) => (D.rel b t, F.erase b)

open GAS (Ev)

/-- One event of the interval semantics (blocking reading of over-all conditions). -/
def Fire : Config S A → Ev A → Config S A → Prop
  | c, .B b, c' => D.enB b c ∧ c' = D.nextB b c
  | c, .E b, c' => D.enE b c ∧ c' = D.nextE b c

/-- A word of events runs from one configuration to another. -/
def Runs : Config S A → List (Ev A) → Config S A → Prop
  | c, [], c' => c' = c
  | c, e :: x, c'' => ∃ c', D.Fire c e c' ∧ Runs c' x c''

/-! ## Homogeneous event steps -/

/-- A beginning step: the beginnings of the actions in `X` (nonempty, duplicate-free, pairwise
independent), all enabled at `c`, fired together. -/
def BStep (X : List A) : Config S A → Config S A → Prop
  | (t, F), c' => X ≠ [] ∧ X.Nodup ∧ X.Pairwise D.Indep ∧ (∀ b ∈ X, D.enB b (t, F)) ∧
      c' = (D.acqL X t, F ∪ X.toFinset)

/-- An ending step: the endings of the actions in `X`, all enabled at `c`, fired together. -/
def EStep (X : List A) : Config S A → Config S A → Prop
  | (t, F), c' => X ≠ [] ∧ X.Nodup ∧ X.Pairwise D.Indep ∧ (∀ b ∈ X, D.enE b (t, F)) ∧
      c' = (D.relL X t, F \ X.toFinset)

/-- Homogeneous step conservativity: from every coherent configuration, a beginning step
fires iff every order of its beginnings runs, and some order runs iff every order runs; the
same for ending steps. -/
def HSC : Prop :=
  ∀ c, D.Coherent c → ∀ (X : List A) (c' : Config S A), X ≠ [] → X.Nodup →
    ((D.BStep X c c' ↔ ∀ p : List A, p.Perm X → D.Runs c (p.map Ev.B) c') ∧
      ((∀ p : List A, p.Perm X → D.Runs c (p.map Ev.B) c') ↔
        ∃ p : List A, p.Perm X ∧ D.Runs c (p.map Ev.B) c')) ∧
    ((D.EStep X c c' ↔ ∀ p : List A, p.Perm X → D.Runs c (p.map Ev.E) c') ∧
      ((∀ p : List A, p.Perm X → D.Runs c (p.map Ev.E) c') ↔
        ∃ p : List A, p.Perm X ∧ D.Runs c (p.map Ev.E) c'))

/-- The forward half of conservativity: every enabled homogeneous step runs in every order. -/
def HSC_fwd : Prop :=
  ∀ c, D.Coherent c → ∀ (X : List A) (c' : Config S A),
    (D.BStep X c c' → ∀ p : List A, p.Perm X → D.Runs c (p.map Ev.B) c') ∧
    (D.EStep X c c' → ∀ p : List A, p.Perm X → D.Runs c (p.map Ev.E) c')

/-- The backward half of conservativity: every run of a homogeneous word is an enabled step. -/
def HSC_bwd : Prop :=
  ∀ c, D.Coherent c → ∀ (X : List A) (c' : Config S A), X ≠ [] → X.Nodup →
    ((∃ p : List A, p.Perm X ∧ D.Runs c (p.map Ev.B) c') → D.BStep X c c') ∧
    ((∃ p : List A, p.Perm X ∧ D.Runs c (p.map Ev.E) c') → D.EStep X c c')

/-! ## Event transparency and the swap conditions -/

/-- Beginnings are transparent to independent beginnings. -/
def ET_BB : Prop :=
  ∀ c, D.Coherent c → ∀ a b, D.Indep a b → D.enB a c → (D.enB b c ↔ D.enB b (D.nextB a c))

/-- The forward half: a beginning never disables an independent beginning. -/
def ET_BB_fwd : Prop :=
  ∀ c, D.Coherent c → ∀ a b, D.Indep a b → D.enB a c → D.enB b c → D.enB b (D.nextB a c)

/-- The backward half: a beginning never enables an independent beginning. -/
def ET_BB_bwd : Prop :=
  ∀ c, D.Coherent c → ∀ a b, D.Indep a b → D.enB a c → D.enB b (D.nextB a c) → D.enB b c

theorem ET_BB_iff : D.ET_BB ↔ D.ET_BB_fwd ∧ D.ET_BB_bwd :=
  ⟨fun h => ⟨fun c hc a b hab ha => (h c hc a b hab ha).1, fun c hc a b hab ha => (h c hc a b hab ha).2⟩,
   fun h c hc a b hab ha => ⟨h.1 c hc a b hab ha, h.2 c hc a b hab ha⟩⟩

/-- Endings are transparent to the endings of other actions. -/
def ET_EE : Prop :=
  ∀ c, D.Coherent c → ∀ a b, a ≠ b → D.enE a c → (D.enE b c ↔ D.enE b (D.nextE a c))

/-- The forward half: an ending never disables another ending. -/
def ET_EE_fwd : Prop :=
  ∀ c, D.Coherent c → ∀ a b, a ≠ b → D.enE a c → D.enE b c → D.enE b (D.nextE a c)

/-- The backward half: an ending never enables another ending. -/
def ET_EE_bwd : Prop :=
  ∀ c, D.Coherent c → ∀ a b, a ≠ b → D.enE a c → D.enE b (D.nextE a c) → D.enE b c

theorem ET_EE_iff : D.ET_EE ↔ D.ET_EE_fwd ∧ D.ET_EE_bwd :=
  ⟨fun h => ⟨fun c hc a b hab ha => (h c hc a b hab ha).1, fun c hc a b hab ha => (h c hc a b hab ha).2⟩,
   fun h c hc a b hab ha => ⟨h.1 c hc a b hab ha, h.2 c hc a b hab ha⟩⟩

/-- Two adjacent beginnings can be swapped. -/
def J_BB : Prop :=
  ∀ c, D.Coherent c → ∀ a b c', a ≠ b →
    D.Runs c [Ev.B a, Ev.B b] c' → D.Runs c [Ev.B b, Ev.B a] c'

/-- Two adjacent endings can be swapped. -/
def J_EE : Prop :=
  ∀ c, D.Coherent c → ∀ a b c', a ≠ b →
    D.Runs c [Ev.E a, Ev.E b] c' → D.Runs c [Ev.E b, Ev.E a] c'

/-- Two events of the same kind (both beginnings or both endings) of distinct actions. -/
def SameKind : Ev A → Ev A → Prop
  | .B a, .B b => a ≠ b
  | .E a, .E b => a ≠ b
  | _, _ => False

/-- Janicki-soundness: from every coherent configuration, the set of runs is closed under
swapping two adjacent beginnings or two adjacent endings. -/
def JSound : Prop :=
  ∀ c, D.Coherent c → ∀ (x y : List (Ev A)) (e f : Ev A) (c' : Config S A), SameKind e f →
    D.Runs c (x ++ e :: f :: y) c' → D.Runs c (x ++ f :: e :: y) c'

end DAS
end IntervalAgents
