import Init.Data.Nat.Coprime
import Init.Data.Nat.Lemmas

namespace LeanLeanFaithfulness.ExportArithmetic

def OppositeParity (m n : Nat) : Prop :=
  m % 2 ≠ n % 2

theorem odd_of_opposite_parity
    {m n : Nat}
    (hparity : OppositeParity m n) :
    (m + n) % 2 = 1 := by
  unfold OppositeParity at hparity
  have hm := Nat.mod_two_eq_zero_or_one m
  have hn := Nat.mod_two_eq_zero_or_one n
  rw [Nat.add_mod]
  cases hm with
  | inl hm0 =>
      cases hn with
      | inl hn0 =>
          exact False.elim (hparity (hm0.trans hn0.symm))
      | inr hn1 =>
          simp [hm0, hn1]
  | inr hm1 =>
      cases hn with
      | inl hn0 =>
          simp [hm1, hn0]
      | inr hn1 =>
          exact False.elim (hparity (hm1.trans hn1.symm))

theorem gcd_right_two_of_odd
    {a : Nat}
    (ha : a % 2 = 1) :
    Nat.gcd a 2 = 1 := by
  rw [Nat.gcd_eq_iff]
  constructor
  · exact Nat.one_dvd a
  constructor
  · exact Nat.one_dvd 2
  · intro c hca hc2
    have hc : c = 1 := by
      have hcne0 : c ≠ 0 := by
        intro h
        subst c
        simp at hc2
      have hcne2 : c ≠ 2 := by
        intro h
        subst c
        rw [Nat.dvd_iff_mod_eq_zero] at hca
        rw [ha] at hca
        cases hca
      have hcle : c ≤ 2 := Nat.le_of_dvd (by decide) hc2
      cases c with
      | zero =>
          exact False.elim (hcne0 rfl)
      | succ c =>
          cases c with
          | zero =>
              rfl
          | succ c =>
              cases c with
              | zero =>
                  exact False.elim (hcne2 rfl)
              | succ c =>
                  have hle0 : Nat.succ c ≤ 0 :=
                    Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hcle)
                  exact False.elim (Nat.not_succ_le_zero c hle0)
    rw [hc]
    exact Nat.dvd_refl 1

theorem gcd_sum_diff_eq_one
    {m n : Nat}
    (hle : n ≤ m)
    (hcoprime : Nat.Coprime m n)
    (hparity : OppositeParity m n) :
    Nat.gcd (m + n) (m - n) = 1 := by
  have hsumOdd : (m + n) % 2 = 1 := odd_of_opposite_parity hparity
  have hsumCoprimeN : Nat.Coprime (m + n) n := by
    rw [Nat.Coprime, Nat.gcd_add_self_left]
    exact hcoprime.gcd_eq_one
  have hdiff :
      (m + n) - 2 * n = m - n := by
    rw [Nat.two_mul, Nat.add_sub_add_right]
  have hdiffLe : m - n ≤ m + n := by
    exact Nat.le_trans (Nat.sub_le m n) (Nat.le_add_right m n)
  calc
    Nat.gcd (m + n) (m - n)
        = Nat.gcd (m + n) ((m + n) - 2 * n) := by rw [hdiff]
    _ = Nat.gcd (m + n) (2 * n) := by
      rw [Nat.gcd_self_sub_right]
      rw [Nat.two_mul]
      exact Nat.add_le_add_right hle n
    _ = Nat.gcd (m + n) 2 := by
      simpa [Nat.mul_comm] using hsumCoprimeN.symm.gcd_mul_left_cancel_right 2
    _ = 1 := gcd_right_two_of_odd hsumOdd

end LeanLeanFaithfulness.ExportArithmetic
