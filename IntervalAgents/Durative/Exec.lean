import IntervalAgents.Durative.Reach
import IntervalAgents.Durative.Lock
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

/-!
# Executable semantics for durative systems

Decidability instances for the enabledness predicates, a computable run function proved
equal to the relational semantics, and the complete words of a set of actions. Concrete
claims about finite systems are then checked by `decide`.
-/

set_option linter.unusedSectionVars false

namespace IntervalAgents
namespace DAS

open GAS (Ev)

variable {S A : Type} [DecidableEq A] (D : DAS S A)

/-- The action of an event. -/
def _root_.IntervalAgents.GAS.Ev.act : Ev A → A
  | .B a => a
  | .E a => a

section Decidable
variable [∀ a s, Decidable (D.start a s)] [∀ a s, Decidable (D.over a s)]
  [∀ a s, Decidable (D.stop a s)] [∀ a b, Decidable (D.conflict a b)]

instance decEnB (b : A) (c : Config S A) : Decidable (D.enB b c) :=
  match c with
  | (t, F) => inferInstanceAs (Decidable (b ∉ F ∧ (∀ d ∈ F, ¬ D.conflict b d) ∧ D.start b t ∧
      D.over b (D.acq b t) ∧ ∀ d ∈ F, D.over d (D.acq b t)))

instance decEnE (b : A) (c : Config S A) : Decidable (D.enE b c) :=
  match c with
  | (t, F) => inferInstanceAs (Decidable (b ∈ F ∧ D.stop b t ∧ ∀ d ∈ F, d ≠ b → D.over d (D.rel b t)))

instance decIndep (a b : A) : Decidable (D.Indep a b) :=
  inferInstanceAs (Decidable (a ≠ b ∧ ¬ D.conflict a b))

instance decCoherent (c : Config S A) : Decidable (D.Coherent c) :=
  match c with
  | (t, F) => inferInstanceAs (Decidable ((∀ a ∈ F, ∀ b ∈ F, a ≠ b → D.Indep a b) ∧ ∀ a ∈ F, D.over a t))

instance decFires1 (a : A) (s s' : S) [DecidableEq S] : Decidable (D.Fires1 a s s') :=
  decidable_of_iff _ (D.fires1_iff a s s').symm

/-- One event, computably. -/
def fireB (c : Config S A) : Ev A → Option (Config S A)
  | .B b => if D.enB b c then some (D.nextB b c) else none
  | .E b => if D.enE b c then some (D.nextE b c) else none

/-- A word, computably. -/
def runB : Config S A → List (Ev A) → Option (Config S A)
  | c, [] => some c
  | c, e :: x => (D.fireB c e).bind (fun c' => runB c' x)

theorem fire_iff_fireB (c : Config S A) (e : Ev A) (c' : Config S A) :
    D.Fire c e c' ↔ D.fireB c e = some c' := by
  cases e with
  | B b =>
    simp only [Fire, fireB]
    split_ifs with h
    · constructor
      · rintro ⟨-, rfl⟩; rfl
      · intro h'; cases h'; exact ⟨h, rfl⟩
    · constructor
      · rintro ⟨h1, -⟩; exact absurd h1 h
      · intro h'; cases h'
  | E b =>
    simp only [Fire, fireB]
    split_ifs with h
    · constructor
      · rintro ⟨-, rfl⟩; rfl
      · intro h'; cases h'; exact ⟨h, rfl⟩
    · constructor
      · rintro ⟨h1, -⟩; exact absurd h1 h
      · intro h'; cases h'

theorem runs_iff_runB : ∀ (x : List (Ev A)) (c c' : Config S A),
    D.Runs c x c' ↔ D.runB c x = some c' := by
  intro x
  induction x with
  | nil => intro c c'; simp [Runs, runB, eq_comm]
  | cons e x ih =>
    intro c c'
    simp only [Runs, runB]
    constructor
    · rintro ⟨c1, h1, h2⟩
      rw [(D.fire_iff_fireB c e c1).1 h1]
      exact (ih c1 c').1 h2
    · intro h
      cases hf : D.fireB c e with
      | none => rw [hf] at h; cases h
      | some c1 =>
        rw [hf] at h
        exact ⟨c1, (D.fire_iff_fireB c e c1).2 hf, (ih c1 c').2 h⟩

instance decRuns (c : Config S A) (x : List (Ev A)) (c' : Config S A) [DecidableEq S] :
    Decidable (D.Runs c x c') :=
  decidable_of_iff _ (D.runs_iff_runB x c c').symm

section Finite
variable [Fintype S] [Fintype A] [DecidableEq S]

instance decET_BB : Decidable D.ET_BB :=
  inferInstanceAs (Decidable (∀ c, D.Coherent c → ∀ a b, D.Indep a b → D.enB a c →
    (D.enB b c ↔ D.enB b (D.nextB a c))))

instance decET_EE : Decidable D.ET_EE :=
  inferInstanceAs (Decidable (∀ c, D.Coherent c → ∀ a b, a ≠ b → D.enE a c →
    (D.enE b c ↔ D.enE b (D.nextE a c))))

instance decJ_BB : Decidable D.J_BB :=
  inferInstanceAs (Decidable (∀ c, D.Coherent c → ∀ a b c', a ≠ b →
    D.Runs c [Ev.B a, Ev.B b] c' → D.Runs c [Ev.B b, Ev.B a] c'))

instance decJ_EE : Decidable D.J_EE :=
  inferInstanceAs (Decidable (∀ c, D.Coherent c → ∀ a b c', a ≠ b →
    D.Runs c [Ev.E a, Ev.E b] c' → D.Runs c [Ev.E b, Ev.E a] c'))

instance decLock : Decidable D.Lock :=
  inferInstanceAs (Decidable (∀ a b, D.Indep a b → ∀ t, D.over a t → D.over b t → D.stop b t →
    D.over a (D.rel b t)))

end Finite

end Decidable

/-! ## Complete words and their interval orders -/

/-- A word is well formed when every ending is preceded by the beginning of the same action. -/
def WellFormed : List (Ev A) → List A → Bool
  | [], _ => true
  | .B a :: w, seen => WellFormed w (a :: seen)
  | .E a :: w, seen => seen.contains a && WellFormed w seen

/-- Insert `x` at every position of `l`. -/
def insertAll {α : Type} (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: l => (x :: y :: l) :: (insertAll x l).map (fun m => y :: m)

/-- All permutations of a list, by structural recursion (so that the kernel can evaluate it). -/
def perms {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: l => (perms l).flatMap (insertAll x)

/-- All complete words over the actions of `X` (each beginning once and ending once). -/
def completeWords (X : List A) : List (List (Ev A)) :=
  (perms (X.map Ev.B ++ X.map Ev.E)).filter (fun w => WellFormed w [])

/-! ### Completeness of the enumeration

`perms l` contains exactly the permutations of `l`, so `completeWords X` contains every
well-formed arrangement of the events of `X`: the statements about histories quantify over
all complete words, not over a chosen list. -/

theorem mem_insertAll_append {α : Type} (x : α) :
    ∀ (l₁ l₂ : List α), l₁ ++ x :: l₂ ∈ insertAll x (l₁ ++ l₂)
  | [], l₂ => by cases l₂ <;> simp [insertAll]
  | y :: l₁, l₂ => by
      simp only [List.cons_append, insertAll, List.mem_cons, List.mem_map]
      exact Or.inr ⟨l₁ ++ x :: l₂, mem_insertAll_append x l₁ l₂, rfl⟩

theorem perm_of_mem_insertAll {α : Type} (x : α) :
    ∀ (l m : List α), m ∈ insertAll x l → m.Perm (x :: l)
  | [], m, h => by
      simp only [insertAll, List.mem_singleton] at h
      subst h; exact List.Perm.refl _
  | y :: l, m, h => by
      simp only [insertAll, List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨m', hm', rfl⟩
      · exact List.Perm.refl _
      · exact ((perm_of_mem_insertAll x l m' hm').cons y).trans (List.Perm.swap x y l)

theorem perm_of_mem_perms {α : Type} : ∀ (l m : List α), m ∈ perms l → m.Perm l
  | [], m, h => by
      simp only [perms, List.mem_singleton] at h
      subst h; exact List.Perm.refl _
  | x :: l, m, h => by
      simp only [perms, List.mem_flatMap] at h
      obtain ⟨p, hp, hm⟩ := h
      exact (perm_of_mem_insertAll x p m hm).trans ((perm_of_mem_perms l p hp).cons x)

theorem mem_perms_of_perm {α : Type} : ∀ (l m : List α), m.Perm l → m ∈ perms l
  | [], m, h => by
      simp [perms, List.perm_nil.1 h]
  | x :: l, m, h => by
      have hx : x ∈ m := h.symm.subset (by simp)
      obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
      have h' : (l₁ ++ l₂).Perm l := (List.perm_middle.symm.trans h).cons_inv
      simp only [perms, List.mem_flatMap]
      exact ⟨l₁ ++ l₂, mem_perms_of_perm l _ h', mem_insertAll_append x l₁ l₂⟩

theorem mem_perms_iff {α : Type} (l m : List α) : m ∈ perms l ↔ m.Perm l :=
  ⟨perm_of_mem_perms l m, mem_perms_of_perm l m⟩

/-- A word is in `completeWords X` iff it is an arrangement of one beginning and one ending of
each action of `X` in which every ending follows its beginning. -/
theorem mem_completeWords_iff (X : List A) (w : List (Ev A)) :
    w ∈ completeWords X ↔ w.Perm (X.map Ev.B ++ X.map Ev.E) ∧ WellFormed w [] = true := by
  simp only [completeWords, List.mem_filter, mem_perms_iff]

/-- Position of an event in a word (length of the word if absent). -/
def pos (w : List (Ev A)) (e : Ev A) : Nat := (w.idxOf e)

/-- The precedence relation of a word: `a` precedes `b` when `a` ends before `b` begins. -/
def prec (w : List (Ev A)) (a b : A) : Bool := decide (pos w (Ev.E a) < pos w (Ev.B b))

/-- The precedence matrix of a word on the actions `X`. -/
def precMatrix (X : List A) (w : List (Ev A)) : List (List Bool) :=
  X.map (fun a => X.map (fun b => prec w a b))

/-! ### Histories, invariant structures, representability and closedness -/

section Histories
variable [∀ a s, Decidable (D.start a s)] [∀ a s, Decidable (D.over a s)]
  [∀ a s, Decidable (D.stop a s)] [∀ a b, Decidable (D.conflict a b)] [DecidableEq S]

/-- The end-point history over the actions `X` between two configurations: all complete words
over `X` that run from `c0` to `c1`. -/
def history (X : List A) (c0 c1 : Config S A) : List (List (Ev A)) :=
  (completeWords X).filter (fun w => D.runB c0 w == some c1)

theorem mem_history_iff (X : List A) (c0 c1 : Config S A) (w : List (Ev A)) :
    w ∈ D.history X c0 c1 ↔ w ∈ completeWords X ∧ D.Runs c0 w c1 := by
  simp only [history, List.mem_filter, runs_iff_runB, beq_iff_eq]

end Histories

/-- `w0` extends the invariant structure of `H` over `X`: it has every precedence common to
all words of `H`, and reverses no weak precedence (a pair `(a, b)` with `b ≺ a` in no word
of `H`). -/
def extendsInv (X : List A) (H : List (List (Ev A))) (w0 : List (Ev A)) : Bool :=
  X.all fun a => X.all fun b =>
    (!(H.all fun w => prec w a b) || prec w0 a b) && (!(H.all fun w => !prec w b a) || !prec w0 b a)

/-- `H` is representable over `X` when every complete word over `X` that extends the invariant
structure of `H` has the interval order of a word of `H`. -/
def representable (X : List A) (H : List (List (Ev A))) : Bool :=
  (completeWords X).all fun w0 =>
    !(extendsInv X H w0) || H.any (fun w => precMatrix X w == precMatrix X w0)

/-- `H` is closed over `X` when every complete word over `X` with the interval order of a word
of `H` belongs to `H`. -/
def closed (X : List A) (H : List (List (Ev A))) : Bool :=
  (completeWords X).all fun w0 =>
    !(H.any (fun w => precMatrix X w == precMatrix X w0)) || decide (w0 ∈ H)

/-! ## Swap classes

Two words of a history are adjacent when they differ by swapping two neighbouring events of
distinct actions. The class of a word is the connected component of the history under this
relation: the words that can be reached by swaps that stay inside the history (so that both
orders are valid runs with the same end points). It is the abstract analogue of a process. -/

/-- The words obtained from `w` by one adjacent swap of events of distinct actions. -/
def swaps : List (Ev A) → List (List (Ev A))
  | [] => []
  | [_] => []
  | e :: f :: w =>
      (if e.act ≠ f.act then [f :: e :: w] else []) ++ (swaps (f :: w)).map (fun v => e :: v)

/-- One breadth-first round: the words of `H` adjacent to the frontier and not yet visited. -/
def swapFrontier (H visited frontier : List (List (Ev A))) : List (List (Ev A)) :=
  frontier.foldl (fun acc w => (swaps w).foldl
    (fun acc' v => if v ∈ H ∧ v ∉ visited ∧ v ∉ acc' then acc' ++ [v] else acc') acc) []

/-- Breadth-first closure with fuel. -/
def swapBFS (H : List (List (Ev A))) : Nat → List (List (Ev A)) → List (List (Ev A)) → List (List (Ev A))
  | 0, visited, _ => visited
  | n + 1, visited, frontier =>
      match swapFrontier H visited frontier with
      | [] => visited
      | f => swapBFS H n (visited ++ f) f

/-- The swap class of `w` inside `H`: the words of `H` reachable from `w` by adjacent swaps of
events of distinct actions that stay inside `H`. -/
def swapClass (H : List (List (Ev A))) (w : List (Ev A)) : List (List (Ev A)) :=
  swapBFS H H.length [w] [w]

end DAS
end IntervalAgents
