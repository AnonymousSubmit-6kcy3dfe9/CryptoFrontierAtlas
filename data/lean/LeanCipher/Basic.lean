namespace LeanCipher

abbrev Bit := Bool

def bxor : Bit -> Bit -> Bit
  | false, b => b
  | true, b => not b

instance : Add Bit where
  add := bxor

instance : OfNat Bit 0 where
  ofNat := false

instance : OfNat Bit 1 where
  ofNat := true

@[simp]
theorem bxor_self (x : Bit) : x + x = 0 := by
  cases x <;> rfl

@[simp]
theorem bxor_false_right (x : Bit) : x + 0 = x := by
  cases x <;> rfl

@[simp]
theorem bxor_false_left (x : Bit) : 0 + x = x := by
  cases x <;> rfl

@[simp]
theorem bxor_assoc (a b c : Bit) : (a + b) + c = a + (b + c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp]
theorem bxor_comm (a b : Bit) : a + b = b + a := by
  cases a <;> cases b <;> rfl

def LinearMap1 := Bit -> Bit

def linearIdentity : LinearMap1 := id

theorem linearIdentity_add (x y : Bit) :
    linearIdentity (x + y) = linearIdentity x + linearIdentity y := by
  rfl

def nonLinearS : Bit -> Bit := fun _ => true

theorem nonLinearS_is_not_additive :
    ¬ (∀ x y : Bit, nonLinearS (x + y) = nonLinearS x + nonLinearS y) := by
  intro h
  have h00 := h false false
  contradiction

def round (p s : Bit -> Bit) (rk x : Bit) : Bit :=
  p (s x) + rk

def encrypt1 (p s : Bit -> Bit) (rk x : Bit) : Bit :=
  round p s rk x

def outputDiff (e : Bit -> Bit) (alpha x : Bit) : Bit :=
  e (x + alpha) + e x

def TruncatedZero (delta : Bit) : Prop :=
  delta = 0

instance truncatedZeroDecidable (delta : Bit) : Decidable (TruncatedZero delta) := by
  unfold TruncatedZero
  infer_instance

def highProbTruncatedDiff (e : Bit -> Bit) (alpha : Bit) : Prop :=
  ∀ x : Bit, TruncatedZero (outputDiff e alpha x)

def eventCount (e : Bit -> Bit) (alpha : Bit) : Nat :=
  (if TruncatedZero (outputDiff e alpha false) then 1 else 0) +
  (if TruncatedZero (outputDiff e alpha true) then 1 else 0)

def probabilityOne (e : Bit -> Bit) (alpha : Bit) : Prop :=
  eventCount e alpha = 2

theorem constant_layer_has_zero_output_diff (rk alpha : Bit) :
    highProbTruncatedDiff (encrypt1 linearIdentity nonLinearS rk) alpha := by
  intro x
  unfold TruncatedZero outputDiff encrypt1 round linearIdentity nonLinearS
  cases rk <;> rfl

theorem constant_layer_probability_one (rk alpha : Bit) :
    probabilityOne (encrypt1 linearIdentity nonLinearS rk) alpha := by
  unfold probabilityOne eventCount TruncatedZero outputDiff encrypt1 round linearIdentity nonLinearS
  cases rk <;> rfl

theorem exists_high_prob_truncated_diff_for_toy_cipher (rk : Bit) :
    ∃ alpha : Bit,
      highProbTruncatedDiff (encrypt1 linearIdentity nonLinearS rk) alpha := by
  exact ⟨true, constant_layer_has_zero_output_diff rk true⟩

theorem exists_probability_one_truncated_diff_for_toy_cipher (rk : Bit) :
    ∃ alpha : Bit,
      probabilityOne (encrypt1 linearIdentity nonLinearS rk) alpha := by
  exact ⟨true, constant_layer_probability_one rk true⟩

end LeanCipher
