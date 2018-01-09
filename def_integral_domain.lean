--Define intergral as a predicate over a type?
universe u

--Do we have to define them as predicates? --Predicate over type classes?
class zero_ne_one_class' (α : Type u) [has_zero α] [has_one α] :=
(zero_ne_one : 0 ≠ (1:α))
class no_zero_divisors' (α : Type u) [has_mul α] [has_zero α] :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)


class integral_domain' (α : Type u) [comm_ring α][no_zero_divisors' α][zero_ne_one_class' α]:=
()