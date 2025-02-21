import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Basic
import Mathlib.Data.ZMod.Basic
import LeanCopilot

variable {α β : Type} {n : ℕ}

def NVector (α : Type) (n: ℕ) := { l: List α // l.length = n }

instance [Repr α] {n: ℕ} : Repr (NVector α n) where
  reprPrec l _ := repr l.val

@[reducible]
def vec (l: List α) : NVector α l.length := ⟨ l, rfl ⟩

namespace NVector
  def len (_: NVector α n) : ℕ := n

  @[ext]
  theorem ext (l : ℕ) (v w: NVector α l) : v.val = w.val → v = w := by
    intro h
    cases v
    cases w
    simp only at h
    simp only [h]

  @[simp]
  def nil : NVector α 0 := ⟨ [], rfl ⟩

  @[simp]
  def cons (a: α) (v: NVector α n)  : NVector α (n + 1) :=
    ⟨ a :: v.val, by simp [v.prop] ⟩

  @[simp]
  def map (f: α → β) (v: NVector α n) : NVector β n :=
    ⟨ v.val.map f, by rw [List.length_map, v.prop] ⟩

  def zip {n} : NVector α n → NVector β n → NVector (α × β) n
    | ⟨ [], ha ⟩, ⟨ [], _ ⟩  => ⟨ [], ha ⟩
    | ⟨ a::as, (ha : as.length + 1 = n) ⟩,
      ⟨ b::bs, (hb : bs.length + 1 = n) ⟩ =>
      let ⟨ z, hz ⟩ := zip ⟨ as, rfl ⟩ ⟨ bs, by apply Nat.add_one_inj.mp; rw [ha, hb] ⟩
      ⟨ (a, b) :: z, by show z.length + 1 = n; rw [hz, ha] ⟩

  @[simp]
  def get (v: NVector α n) (i: Fin n) : α :=
    let i' : Fin v.1.length := Fin.cast v.prop.symm i
    v.val.get i'

  def get_eq {n} (v: NVector α n) (i: Fin n) : v.get i = v.val[i.val] := by
    simp only [get, List.get_eq_getElem, Fin.coe_cast]

  /-- this is exactly what's needed to rewrite `v.get i` into a `List.getElem` if `n` is a concrete Nat -/
  -- def get_eq_lt {n} [NeZero n] (v: NVector α n) (i : ℕ) (h: i < n) :
  --   v.get ((Fin.instOfNatOfNeZeroNat (a:=i)).ofNat : Fin n) = v.val[i]'(by rw [v.prop]; exact h) := by
  --   simp only [get_eq, OfNat.ofNat, Fin.val_ofNat', Nat.mod_eq_of_lt h]

  @[simp]
  theorem get_map {n} {f: α → β} {v: NVector α n} {i: Fin n} : get (map f v) i = f (get v i) := by
    simp only [get, map, List.get_eq_getElem, Fin.coe_cast, List.getElem_map]

  @[simp]
  def append {m} (v: NVector α n) (w: NVector α m) : NVector α (n + m) :=
    ⟨ v.val ++ w.val, by simp [v.prop, w.prop] ⟩

  @[simp]
  def push (v: NVector α n) (a: α) : NVector α (n + 1) :=
    ⟨ v.val ++ [a], by simp [v.prop] ⟩

  theorem push_of_len_succ {n: ℕ} (v: NVector α (n + 1)) : ∃ as: NVector α n, ∃ a: α, v = push as a := by
    match v with
    | ⟨ [], h ⟩ => cases h
    | ⟨ a::as, h ⟩ =>
      rcases as with _ | ⟨ a', as' ⟩
      · have : n = 0 := by simp_all only [List.length_singleton, self_eq_add_left]
        subst this
        use nil, a
        simp only [Nat.reduceAdd, push, nil, List.nil_append]
      have : as'.length + 1 = n := by simp_all only [List.length_cons, add_left_inj]
      subst this
      obtain ⟨ as'', a'', ih ⟩ := push_of_len_succ ⟨ a' :: as', rfl ⟩
      use cons a as'', a''
      apply ext
      simp only [push, cons, List.cons_append, List.cons.injEq, true_and]
      exact congrArg Subtype.val ih

  -- map over monad
  def mapM {M : Type → Type} {n} [Monad M] (v : NVector (M α) n) : M (NVector α n) :=
    match (v : NVector (M α) n) with
    | ⟨ [], h ⟩ => pure ⟨ [], h ⟩
    | ⟨ a :: as, (h : as.length + 1 = n) ⟩ => do
      let hd ← a
      let tl ← mapM ⟨ as, rfl ⟩
      pure ⟨ hd :: tl.val, by rwa [List.length_cons, tl.prop]⟩

  /- induction principle for NVector.cons -/
  def induct {motive : {n: ℕ} → NVector α n → Prop}
    (h0: motive nil)
    (h1: ∀ {n: ℕ} (a: α) {as: NVector α n}, motive as → motive (cons a as))
    {n: ℕ} (v: NVector α n) : motive v := by
    match v with
    | ⟨ [], prop ⟩ =>
      have : n = 0 := by rw [←prop, List.length_eq_zero]
      subst this
      congr
    | ⟨ a::as, h ⟩ =>
      have : as.length + 1 = n := by rw [←h, List.length_cons]
      subst this
      have ih := induct (n:=as.length) h0 h1 ⟨ as, rfl ⟩
      let h' : motive ⟨ a :: as, rfl ⟩ := h1 a ih
      congr

  /- induction principle for NVector.push -/
  def induct_push {motive : {n: ℕ} → NVector α n → Prop}
    (h0: motive nil)
    (h1: ∀ {n: ℕ} {as: NVector α n} (a: α), motive as → motive (as.push a))
    {n: ℕ} (v: NVector α n) : motive v := by
    match v with
    | ⟨ [], prop ⟩ =>
      have : n = 0 := by rw [←prop, List.length_eq_zero]
      subst this
      congr
    | ⟨ a::as, h ⟩ =>
      have : as.length + 1 = n := by rw [←h, List.length_cons]
      subst this
      obtain ⟨ as', a', ih ⟩ := push_of_len_succ ⟨ a :: as, rfl ⟩
      have ih' : motive as' := induct_push h0 h1 as'
      have h' := h1 a' ih'
      rwa [ih]

    def init {n} (create: Fin n → α) : NVector α n :=
      match n with
      | 0 => nil
      | k + 1 =>
        (init (fun i : Fin k => create i)).push (create k)
end NVector



open List

variable {p : ℕ} [p_prime: Fact p.Prime] [p_pos: NeZero p]

def F p := ZMod p

instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p
instance (p : ℕ) [Fact p.Prime] : Inhabited (F p) := ⟨0⟩
instance (p : ℕ) : CommRing (F p) := ZMod.commRing p

@[simp]
lemma bool_constraint (x: F p) (heq: x * (x - 1) = 0): (x = 0 ∨ x = 1) := by {
  cases (eq_zero_or_eq_zero_of_mul_eq_zero heq) with
  | inl h0 => simp [h0]
  | inr h1 => right; exact (eq_of_sub_eq_zero h1)
}


@[simp]
def pow_2 {n: ℕ} : NVector ℕ n := NVector.init (fun i : Fin n => 2^(i.val))

@[simp]
def bit_composition {n: ℕ} (v: NVector (F p) n) : ℕ :=
  if n == 0
    then 0
  else
    let v' := v.map (f := fun x => x.val)
    let zipped := NVector.zip (pow_2) v'
    let mapped := NVector.map (f := fun x => x.fst * x.snd) zipped
    mapped.val.sum

lemma bit_decomposition_step {n: ℕ} (a: F p) (v: NVector (F p) n):
  bit_composition v + a.val * 2^n = bit_composition (v.push a)
  := by {
    simp
    unfold sum
    unfold map

    cases (n = 0) with
    | inl h => sorry
    | inr h => sorry


    -- sorry
  }


theorem boolean_lt_2 {b : F p} (hb : b = 0 ∨ b = 1) : b.val < 2 := by
  rcases hb with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp [ZMod.val_one]

theorem correct_bit_decomposition {n : ℕ} {v : NVector (F p) n} (H : ∀ x, x ∈ v.val → x * (x - 1) = 0) : bit_composition v ≤ 2^n := by
  apply (NVector.induct_push (motive := fun {n : ℕ} (v) => (q: ∀ a ∈ v.val, a * (a - 1) = 0) → bit_composition v ≤ 2^n))
    (h0 := by simp)
    (h1 := by
      intros m as a ih
      intro h2

      have ha: a ∈ (as.push a).val := by simp

      apply h2 at ha

      have ha2: a = 0 ∨ a = 1 := by exact bool_constraint a ha
      have ha3: a.val < 2 := by exact boolean_lt_2 ha2
      have ha4: a.val ≤ 1 := by exact Nat.le_of_lt_succ ha3

      calc bit_composition (as.push a) = (bit_composition as) + a.val * 2^m := by rw [bit_decomposition_step]
                                      _ ≤ 2^m + a.val * 2^m := by aesop
                                      _ ≤ 2^m + 2^m := by simp; aesop
                                      _ = 2^(m + 1) := by omega
    )
  exact H
