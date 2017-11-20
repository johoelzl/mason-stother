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



lemma polynomial.ext : ∀(p q : polynomial α), p.to_fun = q.to_fun → p = q 
|⟨f, hf⟩ ⟨g, hg⟩ (eq.refl _) := rfl

/- remove later -/
lemma polynomial.ext2 : ∀(p q : polynomial α),∀ h: p.to_fun = q.to_fun, p = q 
|⟨f, hf⟩ ⟨g, hg⟩ (@eq.refl _ _) := eq.refl ⟨_, _⟩ 

/- remove later -/
lemma polynomial.ext3 : ∀(p q : polynomial α),∀ h: p.to_fun = q.to_fun, p = q 
|⟨f, hf⟩ ⟨g, hg⟩ (eq.refl c) := eq.refl ⟨c, hf⟩ 

#print nat.less_than_or_equal

lemma pol_zero_add : ∀ a : (polynomial α ),  0 + a = a :=
assume a,
polynomial.ext _ _ (pol_zero_add_fun a)

lemma pol_add_comm : ∀(p q : polynomial α), p + q = q + p :=
assume p q,
suffices h: (p+q).to_fun = (q+p).to_fun, from polynomial.ext (p+q) (q+p) h,
suffices h1: ∀n:ℕ, (p+q).to_fun n = (q+p).to_fun n, from funext h1,
assume n:ℕ,
have h2: (p+q).to_fun n = p.to_fun n +  q.to_fun n, from rfl,
show p.to_fun n +  q.to_fun n = q.to_fun n + p.to_fun n, by simp


lemma pol_add_zero : ∀ a : (polynomial α ), a + 0 = a :=
assume a,
by simp [pol_zero_add a, pol_add_comm a]

lemma pol_add_assoc : ∀ a b c : polynomial α, a + b + c = a + (b + c):=
assume a b c,
suffices h: (a + b + c).to_fun = (a + (b + c)).to_fun, from polynomial.ext (a + b + c) (a + (b + c)) h,
suffices h1: ∀n:ℕ, (a + b + c).to_fun n = (a + (b + c)).to_fun n, from funext h1,
assume n : ℕ, 
show (a.to_fun n + b.to_fun n + c.to_fun n) = (a.to_fun n + (b.to_fun n + c.to_fun n)), by simp




example [ring α] : -(0:α ) = 0:= by simp

def fun_neg (p : polynomial α ) (n: ℕ) := - p.to_fun n

lemma finite_fun_neg: ∀ (p : polynomial α), ∃n:ℕ, ∀m≥n, fun_neg p m = (0 : α)
|⟨f, n, hf⟩ := ⟨n, assume i hi, 
have h: f i = 0,from hf i hi,
have h1: - f i = 0, from by simp [h],
h1⟩  

instance : has_neg (polynomial α) :=
⟨λ p, ⟨fun_neg p, finite_fun_neg p ⟩⟩ 

lemma pol_add_left_neg : ∀ a : polynomial α, -a + a = 0:= 
assume a,
suffices h : (-a + a).to_fun = (0:polynomial α ).to_fun, from polynomial.ext _ _ h,
suffices h1: ∀n:ℕ, (-a + a).to_fun n = (0:polynomial α ).to_fun n, from funext h1,
assume n:ℕ,
have h2: (-a + a).to_fun n = (-a).to_fun n + a.to_fun n, from rfl,
have h3: (-a).to_fun n + a.to_fun n = 0, from neg_add_self _,
show  (-a).to_fun n + a.to_fun n = (0:polynomial α ).to_fun n, from h3

/-Defining the multiplication-/


def summ : ℕ → (ℕ → α ) →  α 
| 0 g := 0
| (n+1) g := g n + (summ n g) --Should swap the order here?

lemma zero_summ_zero : ∀ n: ℕ, summ n (λ_, (0 : α )) = 0
| 0 := rfl
| (n+1) := 
calc 
summ (n + 1) (λ_, (0 : α )) = (λ_, (0 : α )) n + (summ n (λ_, (0 : α ))) : rfl
... = 0 + (summ n (λ_, (0 : α ))) : rfl
... = (summ n (λ_, (0 : α ))) : by simp
... = 0 : zero_summ_zero n


example (n m : ℕ) (f : ℕ → α): summ (n+m) f = summ n f + summ m (λ i, f (i+n)) :=
by induction m with k ih; simp [*, summ, nat.add_succ]


example (n m : ℕ) (f : ℕ → α): summ (n+m) f = summ n f + summ m (λ i, f (i+n)) :=
begin
  induction m,
  case nat.zero {
    simp [summ]
  },
  case nat.succ k ih
  { exact calc 
    summ (n + nat.succ k) f = f (n + k) + summ (n + k) f: rfl
    ... = f (n + k) + summ n f + summ k (λ i, f (i+n)): by rw [ih, add_assoc]
    ... = summ n f + (f (k + n) + summ k (λ i, f (i+n))): by cc
    ... = summ n f + summ (nat.succ k) (λ (i : ℕ), f (i + n)) : rfl }
end

def fun_mul_aux (a b : ℕ → α ) (n:ℕ) : α := summ n (λ m: ℕ, (a m)*(b (n - m - 1)))--MAybe swap a and b?

def fun_mul (a b : polynomial α) (n :ℕ) : α := fun_mul_aux a.to_fun b.to_fun (n+1)

lemma nat_le_add : ∀n m : ℕ, n ≤ n + m --Lemma not needed, or maybe for below?
|n 0 := le_refl n
|n (k+1) := have h1: n ≤ n + k, from nat_le_add n k, 
have h2: n + k ≤ n + k + 1, from nat.less_than_or_equal.step (nat.less_than_or_equal.refl (n+k)),
show  n≤n+k+1, from (le_trans  h1 h2)

variables a b :ℕ → α 
--#reduce (fun_mul_aux a b (2+1))

/-
lemma ge_or_lt : ∀ m n :ℕ, m ≥ n ∨ m < n:= lt_or_ge _ _

lemma ge_or_lt2 : ∀ m n :ℕ, m ≥ n ∨ m < n:=
begin 
intro, intro, exact have h : m ≥ n ∨ n ≥ m, from le_total _ _,
  begin
  cases h with hl hr,
  left, exact hl,
  right, _
  end
end


lemma lt_to_eq2 : ∀ n m : ℕ, n ≤ m → (∃ k : ℕ, m = n + k) 
|0 m := assume h,  ⟨m, by simp ⟩
|(p+1) m:= assume h, have h1: p + 1 = m ∨ p + 1 < m , 
  from nat.eq_or_lt_of_le h,
  begin cases h1 with done lt,
  exact ⟨0, by simp [done]⟩,
  have h2: (p + 1) + 1 ≤ m, from lt,
  have h3: (∃ s : ℕ, m = (p + 1) + 1 + s), from lt_to_eq2 _ _ h2,
  begin 
     cases h3 with s hs,
     exact ⟨ 1 + s, by simp [hs]⟩ 
     
  end
  end-/

lemma lt_to_eq3: ∀ n m : ℕ, n < m → (∃ s : ℕ, m = n + s)
|n 0 := assume h, absurd h (nat.not_lt_zero _)
|n (k+1) := assume h, have h1: n + 1 ≤ k + 1, from h, 
have h2: n + 1 = k + 1 ∨ n + 1 < k + 1, from nat.eq_or_lt_of_le h1,
begin
cases h2 with done lt,
exact ⟨1, (by simp [done])⟩,
exact have n < k, from nat.pred_le_pred lt, 
have h3: (∃ s : ℕ, k = n + s), from lt_to_eq3 n k this,
  begin 
    cases h3 with s hs,
    exact have h4:  k + 1 = n + s + 1, from (by simp [hs]), ⟨ (s + 1), h4⟩ 
  end
end

/-
lemma lt_to_lt_sub: ∀ n m : ℕ, n < m → 0 < m - n
|n 0 := assume h, absurd h (nat.not_lt_zero _)
|n (k + 1):= assume h, have nat.pred n < k, from nat.pred_le_pred h,
-/

lemma le_to_le_sub2: ∀ n m : ℕ, n ≤ m → 0 ≤ m - n 
|0 0 :=assume h, h
|(s+1) 0 := assume h, have (s+1) = 0, from le_antisymm h (nat.zero_le _), by simp [this]
|0 (k+1):= assume h, by simp [h]
|(s+1) (k+1) := assume h, have nat.pred (s+1) ≤ k, from nat.pred_le_pred h,
have h1: 0 ≤ k - (nat.pred (s+1)), from le_to_le_sub2 (nat.pred (s+1)) k this,
have h2: k - (nat.pred (s+1)) = (k + 1) - (s+1), from (by simp),
show 0 ≤ (k + 1) - (s+1), from h2 ▸ h1






-- ¬ a = b ∨a = b zou decidable moeten zijn. want a = b, or en not zijn decidable. 
-- Alleen moet ik doen nog iets vinden dat de bewering waar maakt, maar als ik dat heb, ben ik er ook.


lemma or_dec (p : Prop) (h : decidable p) : p ∨ ¬ p:=
match h with 
|(is_true h_c) := or.inl h_c
|(is_false h_c) := or.inr h_c
end

lemma or_eq : ∀ a b :ℕ,  a = b ∨ ¬ a = b
| a b := or_dec (a = b) (nat.decidable_eq a b) -- Hoe laat ik zien dat a=b decidable is?

lemma eq_succ : ∀ a b :ℕ, a=b → (a + 1) = (b + 1)
|a b (eq.refl _):= rfl

/-
lemma sub_to_eq : ∀ n m : ℕ, m - n = 0 → m = n
| 0 m h := have h1a: m - 0 = m, from rfl, eq.trans (eq.symm h1a) h
| (k + 1) m h:= have h1: m - (k + 1) = (m - k) - 1, from rfl,
have h1aa: m - (k + 1) + 1 = 1, from eq_succ _ _ h,
have m - (k + 1) + 1 = m - k, from by simp, -- Zelfe probleem weer.
have h1a: m - k = 1, from 
have h2: (m - k) - 1 = (m - 1) - k, from by simp, _
-/




/-
match (m - n) with 
| 0 := absurd h (have ((m - n) = 0), from _, _)
| (k+1):= _
end
-/

/-
lemma lt_to_lt_sub: ∀ n m : ℕ, n < m → 0 < m - n
| 0 0 h:= h
| 0 m h:= h
| n 0 h:= absurd h (nat.not_lt_zero _)
| n m h:=
have n + 1 ≤ m, from h, 
have 0 ≤ m - (n + 1), from le_to_le_sub2 _ _ h,
have 0 < m - (n + 1) + 1, from nat.lt_succ_of_le this,
have m - (n + 1) + 1 = m - n, from by simp [nat.sub]
-/ 



/-  n < m -> n + 1 = m v n + 1 < m geval 1 klaar, geval 2 herhaal,
 hoe laat ik nu zien dat het terminate, 
 en hoe beschrijf ik dit proces uberhaupt? -/

lemma finite_fun_mul : ∀ (p q : polynomial α), ∃n:ℕ, ∀m≥n, (fun_mul p q) m = (0 : α)
|⟨f, n, hf⟩ ⟨g, m, hg⟩:= ⟨n + m + 1, 
  begin 
    simp [fun_mul, fun_mul_aux],  
    intro k, intro hk,  
    simp [summ], exact ( 
        have n + (m + 1) ≥ n, from nat_le_add _ _,
        have hkk: k ≥ n, from le_trans this hk,
        have h: f k = 0, from hf k hkk,
        have hprod: ∀ l: ℕ, (λ (s : ℕ), f s * g (k + 1 - s - 1)) l = 0, 
        from assume l : ℕ,
            have h1 :  l < n ∨ l ≥ n , from lt_or_ge _ _,    
            begin
              cases h1 with hlt hgt,--Must do a case split here l ≥ n and l < n, then we have the λ term equal to 0.  
              exact 
                have hle: l ≤ n, from nat.le_of_lt hlt,
                have h11a: n + (m + 1) + 1 ≤ k + 1 , from nat.succ_le_succ hk,
                have h1a: n + (m + 1) + 1 - l ≤ k + 1 - l, from nat.sub_le_sub_right h11a l,
                have n + (m + 1) + 1 - l = (m + 1) + 1 + n - l, from by simp,
                have (∃p₀  : ℕ, l + p₀  = n), from nat.le.dest (le_of_lt hlt),
                have h₀:  (m + 1) + 1 ≤ n + (m + 1) + 1 - l, 
                    from exists.elim this (assume w, assume hw, 
                        have hw2: w ≤ n, from  
                            have w + l = n, by simp [hw],
                            nat.le.intro this , --by simp [le.intro, hw, (nat.le_of_lt hlt)],
                        have h₁ : n - w = l, from iff.elim_left (iff.symm (@nat.sub_eq_iff_eq_add n w l hw2)) (eq.symm hw), 
                        have (m + 1) + 1 ≤ n + (m + 1) + 1 - l, from 
                            have hh₁ : (m + 1) + 1 + n - l = (m + 1) + 1 + (n - l), from nat.add_sub_assoc hle ((m + 1) + 1),
                            have hh₂ : (m + 1) + 1 + (n - l) = (m + 1) + 1 + (n - (n - w)),  by simp [h₁],
                            have h₂ : n - (n - w) =  w, from nat.sub_sub_self hw2,
                            --have (m + 1) + 1 + (n - (n - w)) = (m + 1) + 1 + w, from (@eq.subst _ (∀ q, (m + 1) + 1 + (n - (n - w)) = (m + 1) + 1 + q ) _ _ this (eq.refl ((m + 1) + 1 + (n - (n - w)))) ),
                            have hh₃ : (m + 1) + 1 + (n - (n - w)) = (m + 1) + 1 + w, by simp [h₂],
                            have hh₄ : (m + 1) + 1 ≤ (m + 1) + 1 + w, from nat.le_add_right _ _,
                            have hh₅ :  n + (m + 1) + 1 - l = (m + 1) + 1 + w, from 
                            calc 
                            n + (m + 1) + 1 - l = n + (m + 1) + 1 - l : rfl
                            ... = (m + 1) + 1 + n - l : by simp
                            ... = (m + 1) + 1 + (n - l) : by rw [hh₁]
                            ... = (m + 1) + 1 + (n - (n - w)) : by rw [hh₂ ]
                            ... = (m + 1) + 1 + w : by rw [hh₃],
                            (eq.symm hh₅) ▸ hh₄,
                        this),
                
                have h22: (m + 1) + 1 ≤ k + 1 - l, from le_trans h₀ h1a,
                /-fix factor -1 -/
                have (m + 1) ≤  k + 1 - l - 1, from nat.pred_le_pred h22,
                have m  ≤  k + 1 - l - 1, from le_trans (nat.le_add_right m 1) this,
                have g (k + 1 - l - 1) = 0, from hg _ this,
                have f l * g (k + 1 - l - 1) = 0, by simp [this], 
                show  (λ (s : ℕ), f s * g (k + 1 - s - 1)) l = 0, from this,  

                /-fix factor -1 -/
                /-
                have m ≤ k + 1 - l, from le_trans (nat.le_add_right m 2) h22,
                have g (k + 1 - l) = 0, from hg _ this,
                have f l * g (k + 1 - l) = 0, by simp [this], 
                show  (λ (s : ℕ), f s * g (k + 1 - s)) l = 0, from this, 
                -/
              exact   
                have f l = 0, from hf _ hgt,
                have f l * g (k + 1 - l - 1) = 0, by simp [this],
                show  (λ (s : ℕ), f s * g (k + 1 - s - 1)) l = 0, from this, 
            end, 

            have (λ (m : ℕ), f m * g (k + 1 - m - 1)) = (λ _, (0: α )), from funext hprod,
            have summ k (λ (m : ℕ), f m * g (k + 1 - m - 1)) = 0, from 
                calc 
                summ k (λ (m : ℕ), f m * g (k + 1 - m - 1)) = summ k (λ _, (0: α )) : this ▸ rfl
                ... = 0 : zero_summ_zero k,
            have h111: f k * g (k + 1 - k - 1) + summ k (λ (m : ℕ), f m * g (k + 1 - m - 1)) = f k * g (k + 1 - k - 1),
                by simp [this],
            have f k = 0, from hf _ hkk,
            have h222: f k * g (k + 1 - k - 1) = 0, from by simp [this],
            show (f k * g (k + 1 - k - 1) + summ k (λ (m : ℕ), f m * g (k + 1 - m - 1)) = 0), from
            calc
            f k * g (k + 1 - k - 1) + summ k (λ (m : ℕ), f m * g (k + 1 - m - 1)) = f k * g (k + 1 - k - 1) : h111
            ... = 0 : h222

            )
        /- have n + (m + 1) = n + 1 + m, by simp, have n + (m + 1) ≥ m, by simp [this], -/ 
  end⟩

              /-
            have (m + 1) + 1 + n - l ≤ (m + 1) + 1, from exists.elim h₀ (assume w, assume hw3,
                have (m + 1) + 1 + n - l = (m + 1) + 1 + (n - l), from nat.add_sub_assoc hle ((m + 1) + 1),
                have (m + 1) + 1 + (n - l) = (m + 1) + 1 + (n - (n - w)),  by simp [hw3],
                have w ≤ n, from (have w + l = n, by simp [hw3], ),
                have n - (n - w) =  w, from nat.sub_sub_self hle,
                have (m + 1) + 1 + n - (n - w) = (m + 1) + 1 + w, by simp,
                -/
              
            /-
            have false, from _,
            have h1b: l ≤ n, from nat.le_of_lt hlt,
            have h1c : 0 - l = 0, from nat.zero_sub l,
            have (m + 1) + 1 ≤ n + (m + 1) + (1 - l)
            have n + (m + 1) + (1 - l) ≥ (m + 1) + 1, from _,
            have k + (1 - l) ≥  (m + 1) + (1), from _,
            --have 0 - l ≤ n - l, from iff.elim_right (nat.sub_le_sub_right_iff )
            have 0 ≤ n - l, from nat.le_of_le_of_sub_le_sub_right h1b this,
            -/
            --_ 


            /-have h3: (∃s : ℕ, l + 1 + s = n), from lt_to_eq3 _ _ _,
            have h4: n - l ≥ 0, from (le_to_le_sub2 _ _) (le_of_lt hlt),
            have h5: m + 1 + n - l ≥ m + 1 + 0, from 
            _ 
            
            k + 1 - l >= n + m + 1 + 1 - l
            TP: n + m + 1 + 1 - l >= m + 1 + 1 gegeven dat l < n
            Makkelijker TP: n - l >= 0 gegeven dat l < n,
            Kan misschien wel makkelijker: l < n -> l - l < n - l -> 0 < n - l.
            l < n -> l = n + a, substituting gives n - l >= 0.          
 
            -/


 /-
      calc 
      f k * g (k + 1 - k) + summ k (λ (m : ℕ), f m * g (k + 1 - m)) =
      f k * g (k + 1 - k) + summ k (λ (m : ℕ), f m * g (k + 1 - m)) : rfl
      ... = 0*g (k + 1 - k) + summ k (λ (m : ℕ), f m * g (k + 1 - m)) : by rw h
      ... = summ k (λ (m : ℕ), f m * g (k + 1 - m)) : by simp,
-/
instance : has_mul (polynomial α) := 
⟨λp q, ⟨fun_mul p q, finite_fun_mul p q⟩⟩

lemma fun_mul_assoc : ∀ a b c : polynomial α, (a * b * c).to_fun = (a * (b * c)).to_fun
|⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ := 
begin
apply funext,
intro n,
simp [(*),fun_mul, fun_mul_aux], 
end

lemma pol_mul_assoc : ∀ a b c : polynomial α, a * b * c = a * (b * c)
|a b c:= 


/-
, 
    exact (
      have n + (m + 1) = n + 1 + m, by simp,
      have n + (m + 1) ≥ m, by simp [this], 
      have k ≥ m, from le_trans this hk, 
      have h: f k = 0, from _,
      calc 
      f k * g (k + 1 - k) + summ k (λ (m : ℕ), f m * g (k + 1 - m)) =
      f k * g (k + 1 - k) + summ k (λ (m : ℕ), f m * g (k + 1 - m)) : rfl
      ... = 0*g (k + 1 - k) + summ k (λ (m : ℕ), f m * g (k + 1 - m)) : by rw h
      ... = summ k (λ (m : ℕ), f m * g (k + 1 - m)) : by simp
  _  
   )
-/


/-
exact calc (f k * g (k + 1 - k) + summ k (λ (m : ℕ), f m * g (k + 1 - m))) =  
 f k * g (k + 1 - k) +  summ k (λ (m : ℕ), f m * g (k + 1 - m)) : rfl,
 ... =  0 +  summ k (λ (m : ℕ), f m * g (k + 1 - m)) : simp [hf,hk]
-/
lemma split_summation: ∀(begin_ steps split :ℕ),
∀(h: split ≤ steps),∀(f: ℕ → α), 
summation_steps begin_ steps f = 
(summation_steps begin_ (split -1) f) + (summation_steps (begin_ + split) (steps-split) f) 
|begin_ steps split h f := _


/-
instance : ring (polynomial α) :=
{ zero := 0,
  add := (+), ... }
-/

end
