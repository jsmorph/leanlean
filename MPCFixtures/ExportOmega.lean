import Init.Data.Nat.Lemmas
import Lean.Elab.Tactic.Omega

namespace MPCFixtures.ExportOmega

theorem nat_linear_bounds
    {a b c d : Nat}
    (h1 : a + 2 * b + c ≤ d)
    (h2 : d + 3 ≤ a + b + c + 6) :
    b ≤ 3 := by
  omega

theorem nat_difference_bounds
    {m n k : Nat}
    (hle : n ≤ m)
    (h1 : m ≤ n + k)
    (h2 : k ≤ 4) :
    m - n ≤ 4 := by
  omega

end MPCFixtures.ExportOmega
