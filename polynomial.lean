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


import .auxiliary


structure polynomial (α : Type) [ring α] : Type :=
(to_fun : ℕ → α)
(finite : ∃n:ℕ, ∀m≥n, to_fun m = 0)

section

variables {α : Type} [ring α]

instance : has_zero (polynomial α) :=
⟨⟨(λn, 0), ⟨0, assume (n : ℕ) _, rfl⟩⟩⟩

private def pC (a : α) : ℕ → α
| 0 := a
| _ := 0

private lemma finite_pC {a : α} : ∀m:ℕ, m ≥ 1 → pC a m = 0
| 0 h := absurd h dec_trivial
| (n + 1) h := rfl

def C (a : α) : polynomial α := ⟨pC a, 1, finite_pC⟩

private def fun_X (n : ℕ) : α := if n = 1 then 1 else 0

private lemma finite_X : ∀m:ℕ, m ≥ 2 → fun_X m = (0 : α)
| 0 h := absurd h dec_trivial
| 1 h := absurd h dec_trivial
| (n + 2) h := eq.refl (fun_X (n + 2))

def X : polynomial α := ⟨fun_X, 2, finite_X⟩

def fun_add (p q : polynomial α) (n : ℕ) : α := p.to_fun n + q.to_fun n

lemma finite_fun_add : ∀ (p q : polynomial α), ∃n:ℕ, ∀m≥n, (fun_add p q) m = (0 : α) 
| ⟨f, n, hf⟩ ⟨g, m, hg⟩ := ⟨max n m, assume i hi, 
    have hin: i ≥ n, from le_trans (le_max_left _ _) hi, 
    have him: i ≥ m, from le_trans (le_max_right _ _) hi,
    by simp [fun_add, hin, him, hf, hg]⟩   

instance : has_add (polynomial α) := 
⟨λp q, ⟨fun_add p q, finite_fun_add p q⟩⟩

lemma pol_zero_add_fun : ∀ a : (polynomial α ), (0 + a).to_fun = a.to_fun:= 
assume a : polynomial α, 
have h0: 0 + a = 0 + a, from eq.refl _,

have h2: ∀n:ℕ, fun_add 0 a n = a.to_fun n, from 
assume n:ℕ, zero_add (a.to_fun n),  
show fun_add 0 a = a.to_fun, from funext h2


lemma pol_zero_add_finite : ∀ a : (polynomial α), (∃n:ℕ, ∀m≥n, (((0 +  a).to_fun m) = (0 : α))) = (∃n:ℕ, ∀m≥n, ((a.to_fun m) = (0 : α))):= 
assume a : (polynomial α),
suffices h: (∃n:ℕ, ∀m≥n, (((0 + a).to_fun m) = (0 : α))) ↔ (∃n:ℕ, ∀m≥n, ((a.to_fun m) = (0 : α))), from propext h,
⟨
  assume h1, match h1 with 
  |⟨number,hn⟩:= ⟨number, assume i hi,
   have h2:fun_add 0 a i = 0, from hn i hi,have h3:fun_add 0 a = a.to_fun, from pol_zero_add_fun a, 
   h3 ▸ h2
   ⟩  
  end

, assume h1, match h1 with 
  |⟨number,hn⟩:= ⟨number, assume i hi,
   have h2: a.to_fun i = 0, from hn i hi,have h3:fun_add 0 a = a.to_fun, from pol_zero_add_fun a, 
   have h4: a.to_fun = fun_add 0 a, from eq.symm h3,
   @eq.subst _ (λ x : ℕ → α , (x i = 0) ) a.to_fun (fun_add 0 a) h4 h2
   ⟩  
  end⟩  

lemma pol_zero_add_finite_iff : ∀ a : (polynomial α), (∃n:ℕ, ∀m≥n, (((0 +  a).to_fun m) = (0 : α))) ↔  (∃n:ℕ, ∀m≥n, ((a.to_fun m) = (0 : α))):= 
assume a : (polynomial α),
⟨
  assume h1, match h1 with 
  |⟨number,hn⟩:= ⟨number, assume i hi,
   have h2:fun_add 0 a i = 0, from hn i hi,have h3:fun_add 0 a = a.to_fun, from pol_zero_add_fun a, 
   h3 ▸ h2
   ⟩  
  end

, assume h1, match h1 with 
  |⟨number,hn⟩:= ⟨number, assume i hi,
   have h2: a.to_fun i = 0, from hn i hi,have h3:fun_add 0 a = a.to_fun, from pol_zero_add_fun a, 
   have h4: a.to_fun = fun_add 0 a, from eq.symm h3,
   @eq.subst _ (λ x : ℕ → α , (x i = 0) ) a.to_fun (fun_add 0 a) h4 h2
   ⟩  
  end⟩  

#check λ a :(polynomial α), (∃n:ℕ, ∀m≥n, (((a + 0) m)= (0 : α))) 

lemma pol_zero_add2 : ∀ a : (polynomial α ), a = 0 + a
|⟨f, i, hi⟩ := 
have h: (⟨f, i, hi⟩: polynomial α ) = ⟨f, i, hi⟩, from rfl,
have h2: exists.intro i hi =  (0 + (⟨f, i, hi⟩:polynomial α) ).finite, from _, 
have h1: (⟨f, i, hi⟩: polynomial α ) = 0 + ⟨f, i, hi⟩ , from _,
--have h1: (⟨f, i, hi⟩: polynomial α ) = ((0:polynomial α ) + ⟨f, i, hi⟩), from _,
_ 
 
lemma add_zero : ∀ a : α, a + 0 = a := sorry

/-
instance : ring (polynomial α) :=
{ zero := 0,
  add := (+), ... }
-/

end
