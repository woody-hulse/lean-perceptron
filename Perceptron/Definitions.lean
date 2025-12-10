import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open BigOperators Finset

/-- A labeled point with n features -/
structure LabeledPoint (n : ℕ) where
  features : Fin n → ℚ
  label : ℚ -- 1 or -1

/- Simple operations -/

def dot {n : ℕ} (v w : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, v i * w i

def norm_sq {n : ℕ} (v : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, (v i) ^ 2

def sign (x : ℚ) : ℚ := if x ≥ 0 then 1 else -1

/-- Augment a feature vector by appending 1 (for bias term) -/
def augment {n : ℕ} (x : Fin n → ℚ) : Fin (n + 1) → ℚ :=
  Fin.snoc x 1

def valid_label (y : ℚ) : Prop := y = 1 ∨ y = -1
def valid_labels {n : ℕ} (data : List (LabeledPoint n)) : Prop :=
  ∀ dp ∈ data, valid_label dp.label

theorem valid_label.sq_eq_one {y : ℚ} (h : valid_label y) : y ^ 2 = 1 := by
  cases h with
  | inl h => simp [h]
  | inr h => simp [h]

/-- The margin of a weight vector on a data point: y * (w · x_aug) -/
def margin {n : ℕ} (w : Fin (n + 1) → ℚ) (dp : LabeledPoint n) : ℚ :=
  dp.label * dot w (augment dp.features)

/-- Data points are separable with margin γ if ∃ w* s.t. all points have margin at least γ -/
def separable {n : ℕ} (data : List (LabeledPoint n)) (γ : ℚ) : Prop :=
  ∃ w_star : Fin (n + 1) → ℚ, norm_sq w_star = 1 ∧ γ > 0 ∧ ∀ dp ∈ data, margin w_star dp ≥ γ

def max_norm_sq {n : ℕ} (data : List (LabeledPoint n)) : ℚ :=
  data.foldl (fun acc dp => max acc (norm_sq (augment dp.features))) 0

def zero_vec (n : ℕ) : Fin n → ℚ := fun _ => 0
