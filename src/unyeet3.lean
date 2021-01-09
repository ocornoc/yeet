import tactic data.nat.digits .yeet

theorem unyeetable_3p2 : ¬ ∃ b, yeet b 3 2 :=
begin
  rintro ⟨b, h⟩,
  unfold yeet at h,
  cases b, { change 9 = 3 at h, norm_num at h },
  cases b, { change 9 = 5 at h, norm_num at h },
  cases b, { norm_num [nat.of_digits] at h },
  cases b, { norm_num [nat.of_digits] at h },
  have h2b : 2 < b + 4 := by linarith,
  have h3b : 3 < b + 4 := by linarith,
  rw nat.digits_of_lt _ _ dec_trivial h2b at h,
  rw nat.digits_of_lt _ _ dec_trivial h3b at h,
  change 9 = nat.of_digits _ [3, 2] at h,
  change 9 = 3 + (b + 4) * 2 at h,
  rw [add_mul, ←add_assoc, add_comm, ←add_assoc] at h,
  exact absurd (le_trans (le_add_right (le_refl _)) (ge_of_eq h)) dec_trivial
end

theorem unyeetable_3p4 : ¬ ∃ b, yeet b 3 4 :=
begin
  rintro ⟨b, h⟩,
  unfold yeet at h,
  cases b, { change _ = 3 at h, norm_num at h },
  cases b, { change _ = 7 at h, norm_num at h },
  cases b, { norm_num [nat.of_digits] at h },
  cases b, { norm_num [nat.of_digits] at h },
  cases b, { norm_num [nat.of_digits] at h },
  have h3b : 3 < b + 5 := by linarith,
  have h4b : 4 < b + 5 := by linarith,
  rw nat.digits_of_lt _ _ dec_trivial h3b at h,
  rw nat.digits_of_lt _ _ dec_trivial h4b at h,
  norm_num [nat.of_digits] at h,
  apply_fun (% 4) at h,
  norm_num at h
end
