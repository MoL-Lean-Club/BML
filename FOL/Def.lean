/-
Copyright (c) 2026 MoL Lean Club. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: see COLLABORATORS.md
-/

import Mathlib.Tactic.Tauto

namespace FOL

inductive Formula (Variable : Type) (Predicate : Nat → Type) : Type where
  | eq (x y : Variable)
  | not (f : Formula Variable Predicate)
  | and (f1 f2 : Formula Variable Predicate)
  | some (x : Variable) (f : Formula Variable Predicate)
  | predicate (n : Nat) (p : Predicate n) (vars : Fin n → Variable)

variable {Variable : Type}
variable {Predicate : Nat → Type}

def or : Formula Variable Predicate → Formula Variable Predicate → Formula Variable Predicate
 | f1, f2 => (f1.not.and f2.not).not

def implies : Formula Variable Predicate → Formula Variable Predicate → Formula Variable Predicate
 | f1, f2 => or f1.not f2

def iff : Formula Variable Predicate → Formula Variable Predicate → Formula Variable Predicate
 | f1, f2 => (implies f1 f2).and (implies f2 f1)

def all : Variable → Formula Variable Predicate → Formula Variable Predicate
 | x, f => (f.not.some x).not

structure Model (Domain : Type) (Predicate : Nat → Type) where
  /-- to evaluate predicates -/
  pred : (n : Nat) → Predicate n → (Fin n → Domain) → Prop

variable {Domain : Type}
variable {M : Model Domain Predicate}
variable {s : Variable → Domain}
variable {f1 f2 : Formula Variable Predicate}
variable {x : Variable}

def eval (M : Model Domain Predicate) (s : Variable → Domain) : Formula Variable Predicate → Prop
  | .eq x y => s x = s y
  | .not f => ¬ eval M s f
  | .and f1 f2 => eval M s f1 ∧ eval M s f2
  | .some x f => ∃ s' : Variable → Domain, (∀ y, y ≠ x → s' y = s y) ∧ eval M s' f
  | .predicate n p vars => M.pred n p (fun i => s (vars i))

def eval_global (M : Model Domain Predicate) : Formula Variable Predicate → Prop
  | f => ∀ s : Variable → Domain, eval M s f

@[simp]
lemma eval_not : eval M s f1.not ↔ ¬ eval M s f1 := by
  rfl

@[simp]
lemma eval_and : eval M s (f1.and f2) ↔ eval M s f1 ∧ eval M s f2 := by
  rfl

@[simp]
lemma eval_some :
    eval M s (.some x f1) ↔ ∃ s' : Variable → Domain, (∀ y, y ≠ x → s' y = s y) ∧ eval M s' f1 := by
  rfl

@[simp]
lemma eval_or : eval M s (or f1 f2) ↔ eval M s f1 ∨ eval M s f2 := by
  unfold or
  simp only [eval, not_and, not_not]
  tauto

@[simp]
lemma eval_implies : eval M s (implies f1 f2) ↔ (eval M s f1 → eval M s f2) := by
  unfold implies
  simp only [eval_or, eval_not]
  tauto

@[simp]
lemma eval_iff : eval M s (iff f1 f2) ↔ (eval M s f1 ↔ eval M s f2) := by
  unfold FOL.iff
  simp only [eval, eval_implies]
  tauto

@[simp]
lemma eval_all :
    eval M s (all x f1) ↔ ∀ s' : Variable → Domain, (∀ y, y ≠ x → s' y = s y) → eval M s' f1 := by
  unfold FOL.all
  simp only [eval, not_exists, not_and, not_not]

end FOL
