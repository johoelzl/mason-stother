--Define intergral as a predicate over a type?
universe u

--Do we have to define them as predicates? --Predicate over type classes?
class zero_ne_one_class' (α : Type u) [has_zero α] [has_one α] : Prop :=
(zero_ne_one : 0 ≠ (1:α))

class no_zero_divisors' (α : Type u) [has_mul α] [has_zero α] : Prop :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)

instance no_zero_divisors.to_no_zero_divisors' (α : Type u) [s : no_zero_divisors α] : no_zero_divisors' α :=
⟨s.eq_zero_or_eq_zero_of_mul_eq_zero⟩

instance zero_ne_one_class.to_zero_ne_one_class' (α : Type u) [s : zero_ne_one_class α] : zero_ne_one_class' α :=
⟨s.zero_ne_one⟩

--What is special about a type being a prop?
class integral_domain'' (α : Type u) [comm_ring α] extends no_zero_divisors' α, zero_ne_one_class' α : Prop

class integral_domain' (α : Type u) [comm_ring α][no_zero_divisors' α][zero_ne_one_class' α]

variable {α : Type u}
section no_zero_divisors
variables [has_mul α][has_zero α][no_zero_divisors' α]

lemma eq_zero_or_eq_zero_of_mul_eq_zero'  {a b : α} (h : a * b = 0) : a = 0 ∨ b = 0 :=
no_zero_divisors'.eq_zero_or_eq_zero_of_mul_eq_zero a b h
--#check eq_zero_or_eq_zero_of_mul_eq_zero'
lemma eq_zero_of_mul_self_eq_zero'  {a : α} (h : a * a = 0) : a = 0 :=
or.elim (eq_zero_or_eq_zero_of_mul_eq_zero' h) (assume h', h') (assume h', h')
 

end no_zero_divisors

instance integral_domain'.to_domain [comm_ring α][no_zero_divisors' α][zero_ne_one_class' α][integral_domain' α] : domain α :=



section integral_domain
--now test our definitions
  
  variables (a b c d e : α)
  variables [comm_ring α][no_zero_divisors' α][zero_ne_one_class' α][integral_domain' α]
  --include s

  --instance integral_domain.to_domain : domain α := {..s}
  --set_option pp.numerals false
  set_option pp.implicit true

  
  lemma mul_eq_zero_iff_eq_zero_or_eq_zero' {a b : α} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero', λo,
    or.elim o (λh, by rw h; apply zero_mul) (λh, by rw h; apply mul_zero)⟩

  lemma mul_ne_zero' {a b : α} (h₁ : a ≠ 0) (h₂ : b ≠ 0) : a * b ≠ 0 :=
  λ h, or.elim (eq_zero_or_eq_zero_of_mul_eq_zero' h) (assume h₃, h₁ h₃) (assume h₄, h₂ h₄)

  lemma eq_of_mul_eq_mul_right' {a b c : α} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have b * a - c * a = 0, from sub_eq_zero_of_eq h,
  have (b - c) * a = 0,   by rw [mul_sub_right_distrib, this],
  have b - c = 0,         from (eq_zero_or_eq_zero_of_mul_eq_zero' this).resolve_right ha,
  eq_of_sub_eq_zero this

  lemma eq_of_mul_eq_mul_left' {a b c : α} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have a * b - a * c = 0, from sub_eq_zero_of_eq h,
  have a * (b - c) = 0,   by rw [mul_sub_left_distrib, this],
  have b - c = 0,         from (eq_zero_or_eq_zero_of_mul_eq_zero' this).resolve_left ha,
  eq_of_sub_eq_zero this

  lemma eq_zero_of_mul_eq_self_right' {a b : α} (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  have hb : b - 1 ≠ 0, from
    assume : b - 1 = 0,
    have b = 0 + 1, from eq_add_of_sub_eq this,
    have b = 1,     by rwa zero_add at this,
    h₁ this,
  have a * b - a = 0,   by simp [h₂],
  have a * (b - 1) = 0, by rwa [mul_sub_left_distrib, mul_one],
    show a = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero' this).resolve_right hb

  lemma eq_zero_of_mul_eq_self_left' {a b : α} (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  eq_zero_of_mul_eq_self_right' h₁ (by rwa mul_comm at h₂)

  lemma mul_self_eq_mul_self_iff' (a b : α) : a * a = b * b ↔ a = b ∨ a = -b :=
  iff.intro
    (assume : a * a = b * b,
      have (a - b) * (a + b) = 0,
        by rewrite [mul_comm, ← mul_self_sub_mul_self_eq, this, sub_self],
      have a - b = 0 ∨ a + b = 0, from eq_zero_or_eq_zero_of_mul_eq_zero' this,
      or.elim this
        (assume : a - b = 0, or.inl (eq_of_sub_eq_zero this))
        (assume : a + b = 0, or.inr (eq_neg_of_add_eq_zero this)))
    (assume : a = b ∨ a = -b, or.elim this
      (assume : a = b,  by rewrite this)
      (assume : a = -b, by rewrite [this, neg_mul_neg]))

  lemma mul_self_eq_one_iff' (a : α) : a * a = 1 ↔ a = 1 ∨ a = -1 :=
  have a * a = 1 * 1 ↔ a = 1 ∨ a = -1, from mul_self_eq_mul_self_iff' a 1,
  by rwa mul_one at this




  theorem eq_of_mul_eq_mul_right_of_ne_zero' {a b c : α} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have b * a - c * a = 0, by simp [h],
  have (b - c) * a = 0, by rewrite [mul_sub_right_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero' this).resolve_right ha,
  eq_of_sub_eq_zero this

  
  theorem eq_of_mul_eq_mul_left_of_ne_zero' {a b c : α} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have a * b - a * c = 0, by simp [h],
  have a * (b - c) = 0, by rewrite [mul_sub_left_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero' this).resolve_left ha,
  eq_of_sub_eq_zero this

  

  theorem mul_dvd_mul_iff_left' {a b c : α} (ha : a ≠ 0) : a * b ∣ a * c ↔ b ∣ c :=
  exists_congr $ λ d, by rw [mul_assoc, domain.mul_left_inj ha]

  theorem mul_dvd_mul_iff_right' {a b c : α} (hc : c ≠ 0) : a * c ∣ b * c ↔ a ∣ b :=
  exists_congr $ λ d, by rw [mul_right_comm, domain.mul_right_inj hc]

end integral_domain
instance field.to_integral_domain' [field α] : integral_domain' α := by constructor


variable [s : field α]
variable [integral_domain α]
