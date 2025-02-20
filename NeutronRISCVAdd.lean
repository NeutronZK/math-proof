import LeanCopilot
import Mathlib.Data.ZMod.Basic
import Aesop
import Paperproof

/- Borrowed from cLean -/
def F (p : ℕ) := ZMod p

instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p
instance (p : ℕ) [Fact p.Prime] : Inhabited (F p) := ⟨0⟩
instance (p : ℕ) : CommRing (F p) := ZMod.commRing p
--------------------------

/-
  Main variables and constraints:
  m: Natural number (typically representing a modulus, e.g., 2^32)
  p: Prime number satisfying p > 2m
-/
variable {m: Nat}
variable {p : ℕ}[p_prime: Fact p.Prime][h_p_m: Fact (p > 2 * m)]

/-
  Helper lemmas and theorems for arithmetic operations
-/

/-- Proves that a value x in F_p satisfying x(x-1)=0 must be either 0 or 1 -/
lemma bool_constraint (x: F p) (heq: x * (x - 1) = 0): (x = 0 ∨ x = 1) := by {
  cases (eq_zero_or_eq_zero_of_mul_eq_zero heq) with
  | inl h0 => simp [h0]
  | inr h1 => right; exact (eq_of_sub_eq_zero h1)
}

lemma add_modulus_val (x: F p) (h: x.val < m): (x + m).val = x.val + m := by {
  have h_sum: x.val + m < p :=
    calc
      x.val + m < m + m := by omega
              _ = 2 * m := by ring
              _ < p     := by exact h_p_m.1
  rw [ZMod.val_add x m]
  simp
  exact Nat.mod_eq_of_lt h_sum
}

/-- Handles modulo arithmetic for values between m and 2m -/
lemma mod_between_m_2m (x: ℕ) (h1: x ≥ m) (h2: x < 2 * m): x % m = x - m := by {
  rw [Nat.mod_eq_sub_mod]
  rw [Nat.mod_eq_of_lt]
  omega
  exact h1
}

lemma split_val (x y: F p) (h: x.val + y.val < p):
  ((x + y).val = x.val + y.val) := by
    calc
      (x + y).val =  (x.val + y.val) % p := by exact ZMod.val_add x y
                _ = x.val + y.val := by exact Nat.mod_eq_of_lt h

/--
  Main theorem: AddALU - Verifies the correctness of modular addition

  Parameters:
    * x, y: Input values (< m)
    * z: Result value (< m)
    * ov: Overflow flag (boolean: 0 or 1)

  The theorem proves that the modular addition is correct under the given constraints
-/
theorem AddALU
  (x y z ov: F p)                      -- Witnesses: x, y, z, overflow
  (h_ov_bool: ov * (ov - 1) = 0)       -- Overflow must be boolean (0 or 1)
  (h_eq: x + y - ov * m = z)           -- Main addition constraint
  (h_x: x.val < m)                     -- Range constraint for x
  (h_y: y.val < m)                     -- Range constraint for y
  (h_z: z.val < m)                     -- Range constraint for z
  : ( (x.val + y.val) % m = z.val % m) -- Goal: modular addition of m-bit unsigned integer correctness
  := by

    apply bool_constraint at h_ov_bool

    have h_2m: x.val + y.val < 2 * m := by omega

    have hz: z.val % m = z.val := Nat.mod_eq_of_lt h_z

    have sum_xy: x.val + y.val < p :=
      calc x.val + y.val < m + m := by omega
                      _ = 2 * m := by omega
                      _ < p := by exact h_p_m.1

    by_cases h1 : x.val + y.val < m
    case pos =>
      have ht: (x.val + y.val) % m = x.val + y.val := Nat.mod_eq_of_lt h1

      rw [ht, hz]

      match h_ov_bool with
      | Or.inl h_ov_0 =>
        rw [h_ov_0] at h_eq
        simp at h_eq
        calc
          x.val + y.val = ( x + y ).val := by rw [split_val]; exact sum_xy
                      _ = z.val := by simp [h_eq]
      | Or.inr h_ov_1 =>
        rw [h_ov_1] at h_eq
        simp at h_eq
        exfalso
        have h_eq_1: x.val + y.val = z.val + m := by
          calc x.val + y.val = (x + y).val := by rw [split_val]; omega
                          _  = (z + m).val := by simp [← h_eq]
                          _  = z.val + m := by rw [add_modulus_val]; omega
        omega
    case neg =>
      rw [Nat.not_lt] at h1
      have ht: (x.val + y.val) % m = x.val + y.val - m := by rw [mod_between_m_2m]; exact h1; exact h_2m
      rw [ht]
      rw [hz]
      match h_ov_bool with
      | Or.inl h_ov_0 =>
        rw [h_ov_0] at h_eq
        simp at h_eq
        exfalso
        have h_eq2: x.val + y.val = z.val :=
          calc x.val + y.val = (x + y).val := by rw [split_val]; omega
                          _  = z.val := by exact congrArg ZMod.val h_eq
        omega
      | Or.inr h_ov_1 =>
        rw [h_ov_1] at h_eq
        simp at h_eq
        calc x.val + y.val - m = (x + y).val - m := by rw [split_val]; omega
                            _  = (x + y - m + m).val - m := by aesop
                            _ = (z + m).val - m := by rw [h_eq]
                            _ = z.val + m - m := by rw [add_modulus_val]; omega
                            _ = z.val := by omega
