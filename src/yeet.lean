import data.nat.digits tactic algebra.big_operators
import data.zmod.basic number_theory.quadratic_reciprocity

open_locale big_operators

def yeet (b n m : ℕ) : Prop :=
n ^ m = nat.of_digits b (nat.digits b n ++ nat.digits b m)

namespace yeet

instance (b n m : ℕ) : decidable (yeet b n m) :=
by apply nat.decidable_eq

end yeet

theorem yeet_25_base_10 : yeet 10 5 2 :=
by unfold yeet nat.digits nat.digits_aux; refl

theorem yeet_1p0_any_base : ∀ b, yeet (b + 1) 1 0
| 0       := by change _ = _; refl
| (n + 1) := by unfold yeet nat.digits nat.digits_aux; refl

theorem yeet_np1_0_base (n : ℕ) : yeet 0 n.succ 1 :=
begin
  unfold yeet nat.digits nat.digits_aux_0,
  rw [pow_one, nat.of_digits_append],
  simp
end

lemma ex_pred_of_s : ∀ n > 0, ∃ m : ℕ, m.succ = n
| 0       h := absurd h dec_trivial
| (n + 1) _ := ⟨n, rfl⟩

lemma self_dvd_poly : ∀ n : ℕ, n.prime → n ∣ (3 ^ n - 3)
| 0       _  := dec_trivial
| 1       _  := dec_trivial
| 2       _  := dec_trivial
| 3       _  := dec_trivial
| (n + 4) hp :=
  begin
    have h := @zmod.pow_card_sub_one_eq_one (n + 4) hp 3 dec_trivial,
    norm_num at h,
    change n + 4 ∣ 3 ^ (n + 4) - 3,
    apply_fun λ x, (x - 1) * 3 at h,
    norm_num [sub_self, sub_mul] at h,
    conv_lhs at h { congr, congr, skip, rw ←@pow_one (zmod (n + 4)) _ 3 },
    rw [←pow_add, add_assoc] at h,
    norm_num at h,
    suffices hzm : (3 : zmod (n + 4)) ^ (n + 4) - 3 = ((3 ^ (n + 4) - 3 : ℕ) : zmod (n + 4)),
    rwa [←zmod.nat_coe_zmod_eq_zero_iff_dvd, ←hzm],
    suffices hle : 3 ≤ 3 ^ (n + 4), { rw nat.cast_sub hle, norm_num },
    change 3 ^ 1 ≤ _,
    rw nat.pow_le_iff_le_right (dec_trivial : 2 ≤ 3),
    linarith
  end

-- proof by Shing Tak Lam
theorem p3_lt_poly (n : ℕ) : (n + 3)^2 < 3^(n + 3) - 3 :=
begin
  suffices : (n+3)^2 + 3 < 3^(n+3), -- much nicer
  { have : 3^0 < 3^(n+3) := nat.pow_lt_pow_of_lt_right dec_trivial dec_trivial,
    omega },
  induction n with k IH,
  { norm_num },
  rw [nat.succ_eq_add_one, add_right_comm],
  rw show (k+3+1)^2 = (k+3)^2 + 2*(k+3) + 1, by ring,
  rw pow_succ 3,
  suffices : (k+3) + 1 < (k+3)^2,
  { linarith },
  rw pow_two,
  show k + 3 + 1 < (k + 3) * (k + 3), by nlinarith
end

lemma ex_pred_of_ss : ∀ n > 1, ∃ m : ℕ, m.succ.succ = n
| 0       h := absurd h dec_trivial
| 1       h := absurd h dec_trivial
| (n + 2) _ := ⟨n, rfl⟩

theorem yeet_3p_odd_prime : ∀ n > 2, nat.prime n → yeet ((3 ^ n - 3) / n) 3 n
| 0       h  _  := absurd h dec_trivial
| 1       h  _  := absurd h dec_trivial
| 2       h  _  := absurd h dec_trivial
| (n + 3) hl hp :=
  begin
    set m := n + 3 with hm,
    unfold yeet,
    suffices hpoly : m < ((3 ^ m - 3) / m),
    have hpolypos : 1 < ((3 ^ m - 3) / m) := by linarith,
    cases ex_pred_of_ss _ hpolypos with w hw,
    change (3 ^ m - 3) with (3 ^ m - 3) at hpoly ⊢,
    rw ←hw at hpoly ⊢,
    have h3ltpoly : 3 < w.succ.succ := by linarith,
    rw nat.digits_of_lt _ _ dec_trivial h3ltpoly,
    rw nat.digits_of_lt _ _ dec_trivial hpoly,
    norm_num [nat.of_digits],
    cases n, { norm_num [m, hw] },
    have : m ∣ 3 ^ m - 3 := self_dvd_poly _ hp,
    rw [hw, nat.div_mul_cancel this, add_comm],
    have h3le3pm : 3 ≤ 3 ^ m,
      { change 3 ^ 1 ≤ _,
        apply nat.pow_le_pow_of_le_right,
        exact dec_trivial,
        exact le_of_lt (lt_trans dec_trivial hl) },
    change _ = 3 ^ m - _ + _,
    rw nat.sub_add_cancel h3le3pm,
    change m < (3 ^ m - 3) / m,
    apply lt_of_mul_lt_mul_right _ (nat.zero_le m),
    rw [nat.div_mul_cancel (self_dvd_poly m hp), ←pow_two, hm],
    exact p3_lt_poly n
  end

def ceil_log (b n : ℕ) : ℕ :=
list.length $ nat.digits b n

@[simp]
theorem ceil_log_zero : ∀ b, ceil_log b 0 = 0
| 0     := rfl
| 1     := rfl
| (n+2) := rfl

@[simp]
theorem ceil_log_pos : ∀ b (n > 0), 0 < ceil_log b n
| _     0     h := absurd h dec_trivial
| 0     (n+1) _ := by norm_num [ceil_log, nat.digits, nat.digits_aux_0]
| 1     (n+1) _ := by norm_num [ceil_log, nat.digits, nat.digits_aux_1]
| (b+2) (n+1) _ := by norm_num [ceil_log, nat.digits, nat.digits_aux]

lemma mod_eq_c_iff_multiple_plus_c (n m l : ℕ) (hm : 0 < m) :
  n % m = l ↔ l < m ∧ ∃ p, n = p * m + l :=
begin
  split,
    { intro h,
      induction h,
      apply and.intro (nat.mod_lt _ hm),
      use n / m,
      rw [mul_comm, add_comm],
      exact eq.symm (nat.mod_add_div n m) },
    { rintro ⟨hl, w, h⟩,
      norm_num [h, nat.add_mod],
      exact nat.mod_eq_of_lt hl }
end

@[simp]
lemma nat.digits_of_base : ∀ b > 1, nat.digits b b = [0, 1]
| 0     h := absurd h dec_trivial
| 1     h := absurd h dec_trivial
| (b+2) h := by norm_num [nat.digits, nat.digits_aux]; split

-- proof by Shing Tak Lam
lemma of_digits_append (b : ℕ) (l1 l2 : list ℕ) :
  nat.of_digits b (l1 ++ l2) = nat.of_digits b l1 + b ^ (l1.length) * nat.of_digits b l2 :=
begin
  induction l1 with hd tl IH,
  { simp [nat.of_digits] },
  { rw [nat.of_digits, list.cons_append, nat.of_digits, IH, list.length_cons, pow_succ],
    ring }
end

-- proof by Shing Tak Lam
theorem nat.digits_split : ∀ b n m,
  nat.of_digits b (nat.digits b n ++ nat.digits b m) = n + m * (b ^ ceil_log b n) :=
begin
  intros b n m,
  rw [of_digits_append b (nat.digits b n) (nat.digits b m), 
      nat.of_digits_digits, nat.of_digits_digits, ceil_log, mul_comm],
end

lemma kendfrey_2_dvd_poly {n : ℕ} (h : 0 < n) : 2 ∣ n * (n - 1) :=
begin
  cases ex_pred_of_s _ h with w hw,
  rw ←hw,
  change _ ∣ w.succ * w,
  cases nat.mod_two_eq_zero_or_one w with h h,
    { exact dvd_mul_of_dvd_right (nat.dvd_of_mod_eq_zero h) _ },
    { apply dvd_mul_of_dvd_left,
      rcases (mod_eq_c_iff_multiple_plus_c _ 2 _ dec_trivial).mp h with ⟨_, v, hv⟩,
      rw hv,
      change 2 ∣ _ * _ + 2,
      conv_rhs { congr, skip, rw [←one_mul 2] },
      rw [←add_mul, mul_comm],
      exact nat.dvd_mul_right _ _ }
end

lemma self_lt_kendfrey_poly (n : ℕ) : n + 5 < ((n + 5) * (n + 4)) / 2 :=
begin
  have hpoly := (@kendfrey_2_dvd_poly (n + 5) dec_trivial),
  have := nat.mod_eq_zero_of_dvd hpoly,
  rcases (mod_eq_c_iff_multiple_plus_c _ 2 _ dec_trivial).mp this with ⟨_, w, hw⟩,
  apply lt_of_mul_lt_mul_right _ (nat.zero_le 2),
  norm_num at hpoly,
  rw nat.div_mul_cancel hpoly,
  exact nat.mul_lt_mul_of_pos_left (dec_trivial : 2 < n + 4) (dec_trivial : 0 < n + 5)
end

theorem kendfrey_conjecture : ∀ n > 0, n ≠ 3 → yeet (n * (n - 1) / 2) n 2
| 0 h _ := absurd h (dec_trivial)
| 1 _ _ := dec_trivial
| 2 _ _ := dec_trivial
| 3 _ h := absurd h (dec_trivial)
| 4 _ _ := by norm_num [yeet, nat.of_digits]
| (n+5) h _ :=
  begin
    norm_num [yeet, nat.digits_split],
    have := nat.mod_eq_zero_of_dvd (kendfrey_2_dvd_poly h),
    rcases (mod_eq_c_iff_multiple_plus_c _ 2 _ dec_trivial).mp this with ⟨_, w, hw⟩,
    norm_num at hw,
    norm_num [hw, add_mul_self_eq, ceil_log],
    have hw2 : (n + 5) * (n + 4) / 2 = w,
      { apply_fun λ x, x / 2 at hw, simp at hw, exact hw },
    norm_num [←hw2, nat.digits_of_lt _ _ h (self_lt_kendfrey_poly _), ←hw],
    linarith
  end

lemma mod_3_eq_0_1_or_2 (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 :=
match n % 3, @nat.mod_lt n 3 dec_trivial with
| 0,     _ := or.inl rfl
| 1,     _ := or.inr $ or.inl rfl
| 2,     _ := or.inr $ or.inr rfl
| k + 3, h := absurd h dec_trivial
end

lemma nyefari_3_dvd_poly {n : ℕ} (h : 0 < n) : 3 ∣ n * (n + 1) * (n - 1) :=
begin
  cases ex_pred_of_s _ h with w hw,
  rw ←hw,
  change _ ∣ (w + 1) * (w + 2) * w,
  rcases mod_3_eq_0_1_or_2 w with h | h | h,
    { exact dvd_mul_of_dvd_right (nat.dvd_of_mod_eq_zero h) _ },
  all_goals
    { apply dvd_mul_of_dvd_left,
      rcases (mod_eq_c_iff_multiple_plus_c _ 3 _ dec_trivial).mp h with ⟨_, v, hv⟩,
      rw [hv, add_assoc], },
    { apply dvd_mul_of_dvd_right,
      exact @nat.dvd_add 3 _ 3 (dvd_mul_left _ _) dec_trivial },
    { apply dvd_mul_of_dvd_left,
      exact @nat.dvd_add 3 _ 3 (dvd_mul_left _ _) dec_trivial }
end

theorem self_lt_nyefari_poly (n : ℕ) : n + 3 < ((n + 3) * (n + 4) * (n + 2) / 3) :=
begin
  have hpoly := (@nyefari_3_dvd_poly (n + 3) dec_trivial),
  have := nat.mod_eq_zero_of_dvd hpoly,
  rcases (mod_eq_c_iff_multiple_plus_c _ 3 _ dec_trivial).mp this with ⟨_, w, hw⟩,
  apply lt_of_mul_lt_mul_right _ (nat.zero_le 3),
  norm_num at hpoly,
  rw [nat.div_mul_cancel hpoly, mul_assoc],
  apply nat.mul_lt_mul_of_pos_left _ (dec_trivial : 0 < n + 3),
  norm_num [mul_add, add_mul],
  rw [add_assoc, add_comm _ (n + 2), ←add_assoc, ←add_assoc],
  exact dec_trivial
end

theorem nyefari_conjecture : ∀ n > 0, n ≠ 2 → yeet (n * (n + 1) * (n - 1) / 3) n 3
| 0 h _ := absurd h (dec_trivial)
| 1 _ _ := dec_trivial
| 2 _ h := absurd h (dec_trivial)
| (n+3) h _ :=
  begin
    norm_num [yeet, nat.digits_split],
    have := nat.mod_eq_zero_of_dvd (nyefari_3_dvd_poly h),
    rcases (mod_eq_c_iff_multiple_plus_c _ 3 _ dec_trivial).mp this with ⟨_, w, hw⟩,
    norm_num at hw,
    change (n + 3) ^ 3 with (n + 3) ^ (2 + 1),
    rw [pow_add, pow_one, pow_two],
    norm_num [hw, nat.pow_add, add_mul_self_eq, ceil_log],
    have hw2 : (n + 3) * (n + 4) * (n + 2) / 3 = w,
      { apply_fun λ x, x / 3 at hw, simp at hw, exact hw },
    unfold ceil_log,
    rw [
      nat.digits_of_lt _ _ h (self_lt_nyefari_poly _), list.length, list.length, hw,
      nat.mul_div_cancel _ (dec_trivial : 3 > 0), pow_one, mul_comm 3 w, ←hw
    ],
    ring,
  end

-- this is the grand prize
theorem ultra_conjecture : ∀ (p > 0) (n > p), yeet ((n ^ p - n) / p) n p :=
sorry
