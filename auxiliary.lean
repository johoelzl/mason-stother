universe u
variables {α : Type u} [decidable_linear_order α]

lemma right_le {a b c : α} (h :(max a b) ≤ c) : b ≤ c := 
have h0 : ¬b > c, from 
  (assume h1: b > c,
  have h2: (max a b ) ≥ b, from (le_max_right a b),
  have h3: c < b, from h1,
  have h4: b ≤ (max a b), from h2,
  have h5: c < (max a b), from lt_of_lt_of_le h3 h4,
  have h6: (max a b) > c, from h5,
  have h7: ¬((max a b) ≤ c), from not_le_of_gt h6,
  show false, from (h7 h)),
show b≤c, from  le_of_not_gt h0

lemma left_le {a b c : α} (h :(max a b) ≤ c) : a ≤ c := 
have h0: (max b a) ≤ c, from (max_comm a b) ▸ h,
show a ≤ c, from right_le h0

namespace nat
def test (k : set nat) (a: ℕ) : ℕ := a
def kk : ℕ := 9
#reduce kk.test {} 


end nat