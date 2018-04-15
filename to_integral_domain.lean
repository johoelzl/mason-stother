import data.finsupp
import algebra.ring
import .to_finset
import .to_multiset
import to_comm_semiring

noncomputable theory

local infix ^ := monoid.pow

open classical multiset
local attribute [instance] prop_decidable
local notation a `~ᵤ` b : 50 := associated a b
universe u
variable {α : Type u}
variable [integral_domain α]

--Should be placed elsewhere
lemma prod_eq_zero_iff_zero_mem' {s : multiset α} : prod s = 0 ↔ (0 : α) ∈ s :=
begin
  split,
  {
    apply multiset.induction_on s,
    {
      simp * at *,
    },
    {
      intros a s h1 h2,
      simp * at *,
      by_cases ha : a = 0,
      {
        simp * at *,
      },
      {
        have h3 : prod s = 0,
        {
          by_contradiction h4,
          have : a * prod s ≠ 0,
          from mul_ne_zero ha h4,
          contradiction,
        },
        simp [h1 h3],
      }
    }
  },
  {
    intro h,
    rcases (exists_cons_of_mem h) with ⟨t, ht⟩,
    subst ht,
    simp * at *,
  }
end

lemma associated_of_dvd_dvd {a b : α}
  (h1 : a ∣ b) (h2 : b ∣ a) : a ~ᵤ b :=
begin
  rcases h2 with ⟨c, h3⟩,
  rcases h1 with ⟨d, h4⟩,
  by_cases h6 : (a = 0),
  {
    have h7 : (b = 0),
    {
      simp [h6] at h4,
      assumption,
    },
    simp * at *,
  },
  {
    have h3b : a = a * (d * c),
    { rwa [h4, mul_assoc] at h3},
    have h5 : a * 1 = a * (d * c),
    { simpa},
    have h7 : 1 = (d * c),
      from eq_of_mul_eq_mul_left h6 h5,
    rw mul_comm _ _ at h7,
    exact ⟨unit_of_mul_eq_one (h7.symm), by rw [h4, unit_of_mul_eq_one, units.val_coe, ←mul_assoc, mul_comm c, mul_assoc, ←h7, mul_one]⟩,
  }
end

lemma dvd_dvd_iff_associated {a b : α}
   : (a ~ᵤ b) ↔ ( a ∣ b) ∧ ( b ∣ a):=
⟨dvd_dvd_of_associated, assume h1, associated_of_dvd_dvd h1.1 h1.2⟩

--irreducible, prime and coprime

def prime (p : α) : Prop :=
p ≠ 0 ∧ ¬ is_unit p ∧ ∀ a b, p ∣ (a * b) → (p ∣ a ∨ p ∣ b)

def irreducible  (p : α) : Prop :=
p ≠ 0 ∧ ¬ is_unit p ∧ ∀d, d∣p → (is_unit d ∨ (d ~ᵤ p))

def irreducible'  (p : α) : Prop :=
p ≠ 0 ∧ ¬ is_unit p ∧ ∀ a b : α, p = a * b → (is_unit a ∨ is_unit b)

lemma irreducible'_of_irreducible {p : α} (h1 : irreducible p): irreducible' p :=
begin
  have : ∀ (a b : α), p = a * b → is_unit a ∨ is_unit b,
  {
    intros a b h5,
    have h7 : (is_unit a ∨ (a ~ᵤ p)),
      from h1.2.2 a ⟨b, h5⟩,
    cases h7,
    {
      simp *
    },
    {
      rcases h7 with ⟨u, h8⟩,
      have h9 : p * 1 = p * (↑u * b),
      {
        subst h8,
        rw [mul_comm _ p, mul_assoc] at h5,
        simpa *,
      },
      have h11 : is_unit b,
      {
        exact ⟨u⁻¹, eq.symm 
            (calc ↑(u⁻¹) = ↑u⁻¹ * 1 : by simp
            ... = ↑u⁻¹ * (↑u * b) : by rw [eq_of_mul_eq_mul_left h1.1 h9]
            ... = _ : by rw [←mul_assoc, units.inv_mul, one_mul])⟩,
      },
      simp [h11]
    }  
  },
  exact ⟨h1.1, h1.2.1, this⟩, 
end

lemma irreducible_of_irreducible' {p : α} (h1 : irreducible' p): irreducible p :=
begin
  have : ∀ (d : α), d ∣ p → is_unit d ∨ (d~ᵤ p),
  {
    intros a h5,
    rcases h5 with ⟨b, h6⟩,
    have h7 : is_unit a ∨ is_unit b,
      from h1.2.2 _ _ h6,
    cases h7,
    {
      simp *,
    },
    {
      have h8 : (a ~ᵤ p),
      {
        rcases h7 with ⟨u ,hu⟩,
        apply exists.intro u⁻¹,
        subst h6,
        subst hu,
        rw [mul_comm a, ←mul_assoc, units.inv_mul, one_mul],
      },
      simp [h8]
    }
  },
  exact ⟨h1.1, h1.2.1, this⟩,
end

lemma irreducible_iff_irreducible'  {p : α} : irreducible p ↔ irreducible' p :=
iff.intro irreducible'_of_irreducible irreducible_of_irreducible'


lemma not_is_unit_of_irreducible {a : α} (h : irreducible a) : ¬ (is_unit a) := h.2.1

lemma dvd_irreducible_of_dvd_mul_unit_irreducible {a b c: α} (h2 : is_unit b)(h3 : irreducible c)(h4 : a ∣ (b * c)) : a ∣ c :=
let ⟨bᵤ, hb⟩ := h2 in
let ⟨d, h5⟩ := h4 in exists.intro ( d*bᵤ.inv) 
    (calc c = 1 * c : by simp
    ... = (↑bᵤ⁻¹* ↑bᵤ) * c : by rw [←units.inv_mul _]
    ... = ↑bᵤ⁻¹ * (↑bᵤ * c) : by simp [mul_assoc]
    ... = ↑bᵤ⁻¹ * (b * c): by rw [hb]
    ... = ↑bᵤ⁻¹ * (a * d): by rw h5
    ... = bᵤ.inv * (a * d): by rw [units.inv_coe]
    ... = (a * d) * bᵤ.inv : by simp [mul_assoc, mul_comm]
    ... = a * (d * bᵤ.inv) : by simp [mul_assoc])


--correct simp?
@[simp] lemma not_irreducible_one : ¬ irreducible (1 : α) :=
begin
  by_contradiction h,
  have : ¬is_unit (1 : α),
    from h.2.1,
  have : is_unit (1 : α),
    from is_unit_one,
  contradiction,
end

@[simp] lemma not_irreducible_zero : ¬ irreducible (0 : α) :=
begin
  by_contradiction h1,
  have : (0 : α) ≠ 0,
    from h1.1,
  contradiction,
end

--Problem with 'a' in the namespace
lemma irreducible_of_associated {p b : α}(h1 : irreducible p)(h2 : p ~ᵤ b) : irreducible b :=
begin   
  rcases h2 with ⟨u, hu⟩,   
  have h7 : (b ≠ 0),
  {
    intro h6,
    simp * at *,
  },
  have h8 : (¬ is_unit b),
  {
    intro h8,
    have h9 : is_unit p,
      from hu.symm ▸ (is_unit_mul_of_is_unit_of_is_unit (is_unit_unit u) h8),
    exact h1.2.1 h9
  },
  have h9 : (∀c, (c∣b → (is_unit c ∨ (c ~ᵤ b)))),
  {
    intros c h9,
    by_cases h10 : is_unit c,
    { simp [h10]},
    {
      have h15 : (c~ᵤ p),
      {
        have h14 : c ∣ p,
        {
          rcases h9 with ⟨d, h11⟩,             
          exact ⟨u * d, by {subst h11, subst hu, rw [←mul_assoc, ←mul_assoc, mul_comm c]}⟩
        },
        have h16: is_unit c ∨ (c~ᵤ p),
          from h1.2.2 c h14,
        simp * at *,
      },
      have h16 : (c~ᵤ b),
        from h15.trans ⟨u, hu⟩,
      simp *,
    }
  },
  exact ⟨h7,h8,h9⟩,
end

lemma unit_mul_irreducible_is_irreducible'  {a b : α}: is_unit a → irreducible b → irreducible (a * b)
| ⟨aᵤ, ha⟩ h2 := 
  have h3 : (b ~ᵤ (a*b)),
    from ⟨aᵤ⁻¹, by {rw [ha, ←mul_assoc, units.inv_mul, one_mul]}⟩,
  irreducible_of_associated h2 h3


lemma irreducible_of_prime  {p : α} (h1 : prime p) : irreducible p :=
begin
  rw prime at h1,
  --rw irreducible,
  have h2 : (p ≠ 0),
  {
    from and.elim_left h1,
  },
  have h3 : (¬ is_unit p),
  from and.elim_left (and.elim_right h1),
  rw [irreducible_iff_irreducible', irreducible'],
  have h4 : ∀ (a b : α), p = a * b → is_unit a ∨ is_unit b,
  {
    intros b c h4a,
    by_cases h4b : (b = 0),
    {
      simp [h4b] at h4a,
      contradiction,
    },
    {
      by_cases h4c : (c = 0),
      {
        simp [h4c] at h4a,
        contradiction,
      }, --no indent here
      have h4 : p ∣ (b * c),
      {
        simp *,
      },
      have h5 : p ∣ b ∨ p ∣ c,
      from and.elim_right (and.elim_right h1) b c h4,
      cases h5,
      {
        have h6 : b ∣ b * c,
        {simp},
        have h7 : b ∣ p,
        {
          apply dvd.trans h6,
          simp *,
        },
        have h8 : (p ~ᵤ b),
        from associated_of_dvd_dvd h5 h7,
        rw associated at h8,
        let u := some h8,
        have h9 : p = ↑u * b,
        from some_spec h8,
        rw [h9, mul_comm b c] at h4a,
        have h10 : ↑u = c,
        from eq_of_mul_eq_mul_right_of_ne_zero h4b h4a,
        have h11 : is_unit c,
        {
          fapply exists.intro u,
          exact eq.symm h10,
        },
        simp *,
      },
      {
        have h6 : c ∣ b * c,
        {simp},
        have h7 : c ∣ p,
        {
          apply dvd.trans h6,
          simp *,
        },
        have h8 : (p ~ᵤ c),
        from associated_of_dvd_dvd h5 h7,
        rw associated at h8,
        let u := some h8,
        have h9 : p = ↑u * c,
        from some_spec h8,
        rw [h9] at h4a,
        have h10 : ↑u = b,
        from eq_of_mul_eq_mul_right_of_ne_zero h4c h4a,
        have h11 : is_unit b,
        {
          fapply exists.intro u,
          exact eq.symm h10,
        },
        simp *,
      }
    }
  },
  exact ⟨h2, h3, h4 ⟩
end


lemma irreducible_of_mul_is_unit {a b c : α} (h1 : irreducible a) (h2 : is_unit b) (h3 : a * b = c) : irreducible c :=
begin
  apply irreducible_of_associated h1,
  exact associated_of_mul_is_unit h2 h3,
end

private lemma succ_eq_succ_iff_eq {n m : ℕ} : nat.succ n = nat.succ m ↔ n = m :=
begin
  split,
    exact nat.succ_inj,
    intro h,
    simp *,
end

private lemma eq_zero_or_exists_eq_succ_succ_of_ne_one {n : ℕ} (h : n ≠ 1) : n = 0 ∨ ∃ m, n = nat.succ (nat.succ m) :=
begin
  by_cases h2 : n = 0,
    {simp *},
    {
      rcases (nat.exists_eq_succ_of_ne_zero h2) with ⟨m, hm⟩,
      subst hm,
      simp * at *,
      rw succ_eq_succ_iff_eq at h,
      rcases (nat.exists_eq_succ_of_ne_zero h) with ⟨s, hs⟩,
      subst hs,
      exact ⟨s, rfl⟩,
    }
end

lemma irreducible_pow {a : α} {n : ℕ} (h : irreducible a) : irreducible (a^n) ↔ n = 1 :=
begin
  split,
  {
    intros h1,
    by_contradiction h2,
    have h3 : n = 0 ∨ ∃ m, n = nat.succ (nat.succ m),
    from eq_zero_or_exists_eq_succ_succ_of_ne_one h2,
    cases h3,
    {
      simp * at *,
    },
    {
      rcases h3 with ⟨m, hm⟩,
      subst hm,
      rw pow_succ at *,
      rw irreducible_iff_irreducible' at h1,
      unfold irreducible' at h1,
      have h4: is_unit a ∨ is_unit (a ^ nat.succ m),
      from h1.2.2 _ _ rfl,
      cases h4,
      {
        have : ¬is_unit a,
        from h.2.1,
        contradiction,
      },
      {
        rw pow_succ at h4,
        rw is_unit_mul_iff_is_unit_and_is_unit at h4,
        have : ¬is_unit a,
        from h.2.1,
        exact this h4.1,
      }
    }

  },
  {
    intro h,
    simp * at *,
  }
end


lemma not_is_unit_prod_of_ne_zero_of_forall_mem_irreducible {s : multiset α} (h1 : s ≠ 0) (h2 : ∀x : α, x ∈ s → irreducible x) : ¬is_unit s.prod :=
begin
  rcases (exists_mem_of_ne_zero h1) with ⟨x, hx⟩,
  have h2b : x ∣ (s.prod),
    from dvd_prod_of_mem _ hx,
  have h3: irreducible x,
    from h2 x hx,
  have h4: ¬is_unit x,
    from not_is_unit_of_irreducible h3,
  exact not_is_unit_of_not_is_unit_dvd h4 h2b,
end

--- GCDs

section gcd_id
variables [has_gcd α] {a b c : α}

lemma gcd_zero_associated_left {f : α} : (gcd f (0 : α)) ~ᵤ f :=
begin
  apply associated_of_dvd_dvd,
  exact gcd_left,
  apply gcd_min,
  simp,
  simp
end

lemma gcd_zero_associated_right {α : Type u} [integral_domain α][has_gcd α] {f : α} : (gcd (0 : α) f) ~ᵤ f :=
begin
  apply associated_of_dvd_dvd,
  exact gcd_right,
  apply gcd_min,
  simp,
  simp
end

lemma gcd_eq_zero_iff_eq_zero_and_eq_zero {α : Type u} [integral_domain α][has_gcd α] {f g : α}  : gcd f g = 0 ↔ f = 0 ∧ g = 0:=
begin
  constructor,
  {
     intro h1,
     by_contradiction h2,
     have h3 : ¬(g = 0 ∧ f = 0),
     {
       rw and.comm at h2,
       exact h2
     },
     simp at *,
     by_cases h4 : (f = 0),
     {
       have h5 : g ≠ 0,
       from h2 h4,
       rw h4 at h1,
       have h6 : ((gcd 0 g) ~ᵤ g),
       from gcd_zero_associated_right,
       rw [h1] at h6,
       have h7 : (g ~ᵤ 0),
       from associated.symm h6,
       rw [associated_zero_iff_eq_zero] at h7,
       contradiction,
     },
     {
       apply h4,
       apply eq_zero_of_zero_dvd,
       rw ← h1,
       exact gcd_left,
     }

  },
  {
    intro h1,
    have h2 : f = 0,
    from and.elim_left h1,
    have h3 : g = 0,
    from and.elim_right h1,
    rw [h2, h3],
    exact gcd_zero_zero_eq_zero
  }
end

--Isn't it associated?
lemma gcd_comm : (gcd a b ~ᵤ  gcd b a) :=
begin
  apply associated_of_dvd_dvd,
  {
    have h1 : gcd a b ∣ a,
    from gcd_left,
    have h2 : gcd a b ∣ b,
    from gcd_right,
    exact gcd_min h2 h1,
  },
  {
    have h1 : gcd b a ∣ b,
    from gcd_left,
    have h2 : gcd b a ∣ a,
    from gcd_right,
    exact gcd_min h2 h1,
  }
end

end gcd_id