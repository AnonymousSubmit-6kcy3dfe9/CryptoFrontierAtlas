import CryptoFrontierAtlas.TuDeng
import LeanCipher.TuDengComplete

namespace CryptoFrontierAtlas

theorem pairCount_eq_tuDengCount (k t : Nat) :
    pairCount k t = LeanCipher.tuDengCount k t := by
  rfl

theorem tu_deng_conjecture_root
    {k t : Nat}
    (hk : 2 ≤ k)
    (htPos : 1 ≤ t)
    (htUpper : t ≤ mersenne k - 1) :
    pairCount k t ≤ 2 ^ (k - 1) := by
  rw [pairCount_eq_tuDengCount]
  apply LeanCipher.TuDengComplete.tu_deng_conjecture_root hk htPos
  simpa [mersenne] using htUpper

theorem tu_deng_conjecture_complete : TuDengConjecture := by
  intro k t hk htPos htUpper
  exact tu_deng_conjecture_root hk htPos htUpper

end CryptoFrontierAtlas
