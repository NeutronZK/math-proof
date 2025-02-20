import LeanCopilot
import Mathlib.Data.ZMod.Basic
import Aesop
import Paperproof

open LeanCopilot

def gpt4 : ExternalGenerator := {
  name := "gpt4"
  host := "localhost"
  port := 23337
}

-- #eval generate gpt4 "2 n is even"

#leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."

#moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."

/-
# Finite Field Implementation and Bit Decomposition

This module provides:
* Definition of finite field F_p for prime p
* Implementation using ZMod p
* A theorem about bit decomposition in F_p
-/

/--
Field F_p represents a finite field of prime order p.
This is implemented using ZMod p where p is prime.
-/
def F (p : ℕ) := ZMod p

section FieldInstances
  /-- Basic field instances and properties for F_p -/
  instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
  instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p
  instance (p : ℕ) [Fact p.Prime] : Inhabited (F p) := ⟨0⟩
  instance (p : ℕ) : CommRing (F p) := ZMod.commRing p
end FieldInstances

section BitDecomposition

  variable {p : ℕ} [p_prime: Fact p.Prime]

  /--
  Theorem proving properties of bit decomposition in F_p.
  -/
  theorem bit_decomposition
    (b : F p)                                                    -- witness bit_i
    (f : ℕ → F p)                                                -- linear combination accumlator
    (hb : b = 0 ∨ b = 1)                                         -- constraint: b is boolean
    (hf0 : f 0 = 0)                                              -- base case: LC = 0
    (hf_rec : ∀ i, (f (i+1)).val = (b.val * (2^i)) + (f i).val)  -- recursive case: LC += b * 2^i
    : ∀ i, (f i).val ≤ 2^i - 1                                   -- conclusion: LC is bounded [0, 2^i - 1]
    := by
    intros i
    induction i with
    | zero =>
      rw [hf0]
      simp
    | succ i ih =>
      rw [hf_rec]

      have h_b_bound : b.val ≤ 1 := by {
        cases hb with
        | inl h0 => rw [h0]; simp
        | inr h1 => rw [h1]; rw [ZMod.val_one]
      }

      calc (b.val) * (2 ^ i) + (f i).val ≤ 1 * (2 ^ i) + (f i).val := by aesop
                                      _  ≤ 2^i + (2^i - 1) := by omega
                                      _  = 2^i * 2 - 1 := by omega
                                      _  = 2^(i+1) - 1 := by omega
end BitDecomposition
