import data.finsupp
import algebra.ring
import .to_finset
import .to_multiset


local infix ^ := monoid.pow


universe u
variable {α : Type u}
variable [semiring α]

def associated (x y : α) : Prop:=
∃u : units α, x = u * y

local notation a `~ᵤ` b : 50 := associated a b

def is_unit (a : α) : Prop := ∃b : units α, a = b

/- is used once in UFD, but I don't understand what it does
-/
lemma is_unit_unit  (u : units α) : @is_unit α _ u :=
⟨u, rfl⟩


@[simp] lemma is_unit_one : is_unit (1 : α ) := ⟨1, rfl⟩

--Should I do all these lemmas using the zero_ne_one class?
@[simp] lemma not_is_unit_zero (h : (0 : α) ≠ 1) : ¬ is_unit (0 : α) := --Do we need semiring?
begin
  intro h,
  rcases h with ⟨u, hu⟩,
  have h2: u.val*u.inv = 1,
    from u.val_inv,
  simp [units.val_coe] at *,
  rw [←hu, _root_.zero_mul] at h2,
  contradiction,
end

lemma ne_zero_of_is_unit {a : α} (h : (0 : α) ≠ 1) : is_unit a → a ≠ 0 :=
begin
  intros h1 h2,
  subst h2,
  exact not_is_unit_zero h h1,
end

lemma is_unit_mul_of_is_unit_of_is_unit {a b : α} (h1 : is_unit a) (h2 : is_unit b) : is_unit (a * b) :=
let ⟨aᵤ, ha⟩ := h1 in
let ⟨bᵤ, hb⟩ := h2 in ⟨aᵤ*bᵤ, by simp [units.mul_coe, *]⟩

lemma zero_associated_zero   : (0 : α) ~ᵤ 0 := ⟨1, by simp⟩

lemma unit_associated_one {u : units α}: (u : α) ~ᵤ 1 := ⟨u, by simp⟩
