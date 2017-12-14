import .poly

universe u
class algebraically_closed_field (α : Type u) [field α] :=
(has_root : ∀ p : polynomial α, ∃k:α, polynomial.root_of p k)