import Mathlib

/-!
# Balanced eight-variable nonlinearity: checked finite certificates

This module formalizes the *trusted integer terminal stage* of the
balanced-eight argument accompanying the paper.  The thirteen profiles are
the exact output of the paper's preceding finite contingency enumeration;
that enumeration and its 69 rational Farkas certificates are not silently
replaced by an assumption here.  What is replayed below is solver-free
arithmetic:

* the fifteen signed magnitude categories and their pointwise terminal
  identities;
* the eleven balanced-profile scores and the two weight-56 scores;
* the strict B2 certificate with right-hand side `-384`;
* the U1/U2 certificates with right-hand sides `-256` and `-384`; and
* the published 256-bit truth table, whose finite Walsh transform has weight
  `128`, maximum absolute coefficient `24`, and nonlinearity `116`.

It deliberately does **not** claim the full theorem that every balanced
eight-variable Boolean function has nonlinearity at most `116`: the bridge
from a hypothetical function to these profiles, the global Farkas replay, and
the inverse-Walsh box inequalities are outside this module's scope.

All claims in this file are closed propositions checked by Lean reduction
with `native_decide`, using its standard native-code reflection trust model.
No theorem takes an unproved bridge as a hypothesis for the omitted global
reduction.
-/

namespace CryptoFrontierAtlas
namespace BalancedEight

-- These local names keep the witness replay independent of the Foundation
-- draft's currently changing API (and avoid shadowing its public names when
-- this module is imported by `CryptoFrontierAtlas.lean`).
abbrev B8BitVec (n : Nat) := Fin n -> Bool

private def b8BoolSign (b : Bool) : Int := if b then -1 else 1

private def b8Dot (x y : B8BitVec n) : Bool :=
  decide ((Finset.univ.filter (fun i => x i && y i)).card % 2 = 1)

private def b8Walsh (f : B8BitVec n -> Bool) (a : B8BitVec n) : Int :=
  ∑ x, b8BoolSign (f x != b8Dot a x)

private def b8HammingWeight (f : α -> Bool) [Fintype α] : Nat :=
  (Finset.univ.filter (fun x => f x = true)).card

/-! ## The thirteen terminal profiles -/

structure Profile where
  n20 : Nat
  n12 : Nat
  n4 : Nat
  n16 : Nat
  n8 : Nat
  n0 : Nat
  deriving DecidableEq, Repr

def profiles : List Profile :=
  [ { n20 := 112, n12 := 8,  n4 := 8,  n16 := 60, n8 := 64, n0 := 4 }
  , { n20 := 112, n12 := 16, n4 := 0,  n16 := 56, n8 := 64, n0 := 8 }
  , { n20 := 114, n12 := 2,  n4 := 12, n16 := 60, n8 := 64, n0 := 4 }
  , { n20 := 116, n12 := 4,  n4 := 8,  n16 := 56, n8 := 64, n0 := 8 }
  , { n20 := 116, n12 := 12, n4 := 0,  n16 := 52, n8 := 64, n0 := 12 }
  , { n20 := 120, n12 := 8,  n4 := 0,  n16 := 48, n8 := 64, n0 := 16 }
  , { n20 := 128, n12 := 0,  n4 := 0,  n16 := 40, n8 := 64, n0 := 24 }
  , { n20 := 113, n12 := 5,  n4 := 10, n16 := 60, n8 := 64, n0 := 4 }
  , { n20 := 117, n12 := 1,  n4 := 10, n16 := 56, n8 := 64, n0 := 8 }
  , { n20 := 105, n12 := 13, n4 := 10, n16 := 70, n8 := 56, n0 := 2 }
  , { n20 := 106, n12 := 10, n4 := 12, n16 := 70, n8 := 56, n0 := 2 }
  , { n20 := 114, n12 := 10, n4 := 4,  n16 := 56, n8 := 64, n0 := 8 }
  , { n20 := 115, n12 := 7,  n4 := 6,  n16 := 56, n8 := 64, n0 := 8 }
  ]

def balancedProfiles : List Profile := profiles.take 9 ++ profiles.drop 11

def unbalancedProfiles : List Profile := profiles.drop 9 |>.take 2

def score (p : Profile) : Int :=
  5 * (p.n20 : Int) - 3 * (p.n12 : Int) + (p.n4 : Int)

def rankBound (s : Nat) : Int := 64 * (2 ^ s : Nat)

theorem profile_score_replay :
    balancedProfiles.map score =
      [544, 512, 576, 576, 544, 576, 640, 560, 592, 544, 560] := by
  norm_num [balancedProfiles, profiles, score]

theorem balanced_profiles_have_n8_64 :
    ∀ p ∈ balancedProfiles, p.n8 = 64 := by
  native_decide

theorem balanced_profiles_exceed_rank_le_two :
    ∀ p ∈ balancedProfiles, ∀ s ∈ [0, 1, 2], rankBound s < score p := by
  native_decide

theorem balanced_profile_score_le_rank_three_only_B2 :
    ∀ p ∈ balancedProfiles, score p ≤ rankBound 3 →
      p = { n20 := 112, n12 := 16, n4 := 0, n16 := 56, n8 := 64, n0 := 8 } := by
  native_decide

/-! ## Signed category identities -/

structure Category where
  pMag : Nat
  qMag : Nat
  deriving DecidableEq, Repr

def categories : List Category :=
  [ { pMag := 1, qMag := 1 }, { pMag := 1, qMag := 3 }
  , { pMag := 1, qMag := 5 }, { pMag := 1, qMag := 7 }, { pMag := 1, qMag := 9 }
  , { pMag := 3, qMag := 1 }, { pMag := 3, qMag := 3 }, { pMag := 3, qMag := 5 }
  , { pMag := 3, qMag := 7 }
  , { pMag := 5, qMag := 1 }, { pMag := 5, qMag := 3 }, { pMag := 5, qMag := 5 }
  , { pMag := 7, qMag := 1 }, { pMag := 7, qMag := 3 }
  , { pMag := 9, qMag := 1 }
  ]

def rho (m : Nat) : Int :=
  if m % 4 = 1 then (m : Int) else -(m : Int)

def sign (b : Bool) : Int := if b then -1 else 1

def categoryParity (c : Category) : Bool :=
  decide (((rho c.pMag * rho c.qMag + 1) / 4) % 2 = 1)

def categoryIs20 (c : Category) : Bool :=
  ((c.pMag = 9 ∧ c.qMag = 1) || (c.pMag = 1 ∧ c.qMag = 9)) ||
    ((c.pMag = 7 ∧ c.qMag = 3) || (c.pMag = 3 ∧ c.qMag = 7)) ||
    (c.pMag = 5 ∧ c.qMag = 5)

def categoryIs12 (c : Category) : Bool :=
  ((c.pMag = 7 ∧ c.qMag = 1) || (c.pMag = 1 ∧ c.qMag = 7)) ||
    ((c.pMag = 5 ∧ c.qMag = 1) || (c.pMag = 1 ∧ c.qMag = 5)) ||
    (c.pMag = 3 ∧ c.qMag = 3)

def categoryIs4 (c : Category) : Bool :=
  ((c.pMag = 5 ∧ c.qMag = 3) || (c.pMag = 3 ∧ c.qMag = 5)) ||
    ((c.pMag = 3 ∧ c.qMag = 1) || (c.pMag = 1 ∧ c.qMag = 3)) ||
    (c.pMag = 1 ∧ c.qMag = 1)

def quadraticPart : Nat → Nat → Bool
  | 0, _ => false
  | r + 1, a =>
      Bool.xor (quadraticPart r a)
        (Nat.testBit a (2 * r) && Nat.testBit a (2 * r + 1))

def canonicalR (r a : Nat) : Bool :=
  Bool.xor (Nat.testBit a (2 * r)) (quadraticPart r a)

def categoryP (weight : Nat) (c : Category) : Int :=
  if weight = 59 then rho c.pMag else -rho c.pMag

def categoryQ (weight : Nat) (c : Category) : Int :=
  if weight = 59 then -rho c.qMag else rho c.qMag

def epsilon (weight : Nat) : Int := if weight = 59 then -1 else 1

def categoryCoefficient (weight r a : Nat) (c : Category) : Int :=
  (2 ^ r : Int) *
      (-10 * (if categoryIs20 c then 1 else 0) +
        6 * (if categoryIs12 c then 1 else 0)) +
    epsilon weight * (-(2 ^ r : Int) * sign (canonicalR r a)) *
      (categoryP weight c - categoryQ weight c)

def nonzeroFrequencies : List Nat := (List.range 128).drop 1

theorem category_pointwise_certificate :
    ∀ weight ∈ [59, 61], ∀ r ∈ [0, 1, 2, 3],
      ∀ a ∈ nonzeroFrequencies, ∀ c ∈ categories,
        canonicalR r a = categoryParity c →
          0 ≤ categoryCoefficient weight r a c ∧
            categoryCoefficient weight r a c =
              (2 ^ (r + 1) : Int) * (if categoryIs4 c then 1 else 0) := by
  native_decide

/-! ## Closed integer terminal certificates -/

def b2CertificateRhs : Int :=
  320 - 40 * 112 + 24 * (16 - 1) + 28 * 122

theorem b2_terminal_certificate : b2CertificateRhs = -384 := by
  norm_num [b2CertificateRhs]

private def dotParity : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | n + 1, a, x =>
      Bool.xor (dotParity n a x) (Nat.testBit a n && Nat.testBit x n)

private def character (a x : Nat) : Int := sign (dotParity 7 a x)

private def b2TerminalSet : List Nat :=
  ((List.range 128).drop 64).filter (fun x => !canonicalR 3 x)

private def b2Transform (a : Nat) : Int :=
  (b2TerminalSet.map (character a)).sum

private def b2PointwiseCertificate (a : Nat) (c : Category) : Int :=
  320 * (if a = 64 then 1 else 0) -
    40 * (if categoryIs20 c then 1 else 0) +
    24 * (if categoryIs12 c then 1 else 0) +
    b2Transform a * (categoryP 61 c - categoryQ 61 c)

theorem b2_terminal_set_cardinality : b2TerminalSet.length = 28 := by
  native_decide

theorem b2_transform_replay :
    ∀ a ∈ nonzeroFrequencies,
      b2Transform a = if a = 64 then -28 else -4 * sign (canonicalR 3 a) := by
  native_decide

theorem b2_pointwise_nonnegative :
    ∀ a ∈ nonzeroFrequencies, ∀ c ∈ categories,
      canonicalR 3 a = categoryParity c → 0 ≤ b2PointwiseCertificate a c := by
  native_decide

theorem b2_pointwise_value_replay :
    ∀ a ∈ nonzeroFrequencies, ∀ c ∈ categories,
      canonicalR 3 a = categoryParity c →
        b2PointwiseCertificate a c = 0 ∨ b2PointwiseCertificate a c = 8 ∨
          b2PointwiseCertificate a c = 264 ∨ b2PointwiseCertificate a c = 512 := by
  native_decide

def unbalancedRhs (p : Profile) : Int :=
  320 - 40 * (p.n20 : Int) + 24 * ((p.n12 : Int) - 1) -
    8 * (p.n4 : Int) + 28 * 122

theorem unbalanced_terminal_scores :
    unbalancedProfiles.map score = [496, 512] := by
  norm_num [unbalancedProfiles, profiles, score]

theorem unbalanced_terminal_certificates :
    unbalancedProfiles.map unbalancedRhs = [-256, -384] := by
  norm_num [unbalancedProfiles, profiles, unbalancedRhs]

theorem unbalanced_rhs_score_identity :
    ∀ p ∈ unbalancedProfiles, unbalancedRhs p = 8 * (464 - score p) := by
  native_decide

private def unbalancedTerminalSet : List Nat :=
  (List.range 64).filter (fun x => quadraticPart 3 x)

private def unbalancedTransform (a : Nat) : Int :=
  (unbalancedTerminalSet.map (character a)).sum

private def unbalancedPointwiseCertificate (a : Nat) (c : Category) : Int :=
  320 * (if a = 64 then 1 else 0) -
    40 * (if categoryIs20 c then 1 else 0) +
    24 * (if categoryIs12 c then 1 else 0) -
    8 * (if categoryIs4 c then 1 else 0) +
    unbalancedTransform a * (categoryP 61 c - categoryQ 61 c)

theorem unbalanced_terminal_set_cardinality : unbalancedTerminalSet.length = 28 := by
  native_decide

theorem unbalanced_transform_replay :
    ∀ a ∈ nonzeroFrequencies,
      unbalancedTransform a = if a = 64 then 28 else -4 * sign (quadraticPart 3 a) := by
  native_decide

theorem unbalanced_pointwise_nonnegative :
    ∀ a ∈ nonzeroFrequencies, ∀ c ∈ categories,
      quadraticPart 3 a = categoryParity c →
        0 ≤ unbalancedPointwiseCertificate a c := by
  native_decide

theorem unbalanced_pointwise_value_replay :
    ∀ a ∈ nonzeroFrequencies, ∀ c ∈ categories,
      quadraticPart 3 a = categoryParity c →
        unbalancedPointwiseCertificate a c = 0 ∨
          unbalancedPointwiseCertificate a c = 256 ∨
            unbalancedPointwiseCertificate a c = 512 := by
  native_decide

/-! ## The explicit nonlinearity-116 witness -/

def witnessWord : Nat :=
  0xee47b888c64d30227cbe575846c1fe42de03879685c95ec9a71be53a54f24976

-- This is the reversal of the artifact's 64 hexadecimal digits, so bit `i`
-- agrees with its explicitly documented least-significant-bit-first order.

def witnessFunction (x : B8BitVec 8) : Bool :=
  Nat.testBit witnessWord
    (∑ i : Fin 8, if x i then 2 ^ (i : Nat) else 0)

def witnessWeight : Nat := b8HammingWeight witnessFunction

def witnessWalshAbs (a : B8BitVec 8) : Nat :=
  Int.natAbs (b8Walsh witnessFunction a)

def witnessMaximumWalshAbs : Nat :=
  (Finset.univ : Finset (B8BitVec 8)).sup witnessWalshAbs

def witnessNonlinearity : Nat := 128 - witnessMaximumWalshAbs / 2

theorem witness_balanced : witnessWeight = 128 := by
  native_decide

theorem witness_maximum_walsh_abs : witnessMaximumWalshAbs = 24 := by
  native_decide

theorem witness_nonlinearity_value : witnessNonlinearity = 116 := by
  native_decide

theorem witness_nonlinearity_116 :
    witnessWeight = 128 ∧ witnessMaximumWalshAbs = 24 ∧
      witnessNonlinearity = 116 :=
  ⟨witness_balanced, witness_maximum_walsh_abs, witness_nonlinearity_value⟩

end BalancedEight
end CryptoFrontierAtlas
