/-
Copyright (c) 2017 Jens Wagemaker, Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jens Wagemaker, Johannes Hölzl

Polynomials and their ring structure
-/

/-

  Polynomials as a ring with the following structure:

    X : polynomial α       -- the formal variable
    C : α → polynomial α   -- a constant polynomial

  now we can represent polynomials like

    $ a_n * X^n + ... + a_0 $

  as

    `C a_n * X ^ n + ... + C a_0`

-/

structure polynomial (α : Type) [ring α] : Type :=
(to_fun : ℕ → α)
(finite : ∃n:ℕ, ∀m≥n, to_fun m = 0)

section
variables {α : Type} [ring α]

instance : has_zero (polynomial α) :=
⟨⟨(λn, 0), _⟩⟩

def pC (a : α) : ℕ → α
| 0 := a
| _ := 0

lemma finite_pC' {a : α} : ∀m:ℕ, m ≥ 1 → pC a m = 0 :=
_

lemma finite_pC {a : α} : ∃n:ℕ, ∀m≥n, pC a m = 0 :=
_

def C₀ (a : α) : polynomial α := ⟨pC a, finite_pC⟩

def C₁ (a : α) : polynomial α :=
⟨(λn, match n with 0 := a | _ := 0 end), _⟩

def C₂ (a : α) : polynomial α :=
⟨(λn, if n = 0 then a else 0), _⟩

def X : polynomial α :=
⟨(λn, if n = 1 then 1 else 0), _⟩

instance : has_add (polynomial α) :=
⟨λp q, ⟨λn, p.to_fun n + q.to_fun n, _⟩⟩

/-
instance : ring (polynomial α) :=
{ zero := 0,
  add := (+), ... }
-/

end
