import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.ZMod.Basic

namespace LeanCipher

/-!
Basic binary-vector API shared by the active Boolean-function modules.

Historical S-box/DDT, BCT, and RSBF developments live in the archive.  This
file intentionally keeps only the small `F2Vec` foundation needed by the
current root-level workflows.
-/

abbrev F2Vec (n : Nat) : Type :=
  Fin n -> ZMod 2

@[simp]
theorem f2vec_add_self {n : Nat} (x : F2Vec n) : x + x = 0 := by
  ext i
  change x i + x i = 0
  rw [<- two_nsmul (x i), CharTwo.two_nsmul]

@[simp]
theorem f2vec_cancel_right {n : Nat} (x c : F2Vec n) :
    x + c + c = x := by
  rw [add_assoc, f2vec_add_self, add_zero]

@[simp]
theorem f2vec_cancel_left {n : Nat} (c x : F2Vec n) :
    c + (c + x) = x := by
  rw [<- add_assoc, f2vec_add_self, zero_add]

end LeanCipher
