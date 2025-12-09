import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open BigOperators Finset

/-- A perceptron with n input features (using n + 1 weights to include bias term) -/
structure Perceptron (n : ℕ) where
  weights : Fin (n + 1) → ℚ

/-- A labeled data point with n features -/
structure DataPoint (n : ℕ) where
  features : Fin n → ℚ
  label : ℚ -- 1 or -1

/-- Augment a feature vector by appending 1 (to remove bias term) -/
def augment {n : ℕ} (x : Fin n → ℚ) : Fin (n + 1) → ℚ :=
  Fin.snoc x 1

def dot {n : ℕ} (v w : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, v i * w i

def normSq {n : ℕ} (v : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, (v i) ^ 2

/-- Sign function: returns 1 if x ≥ 0, else -1 -/
def sign (x : ℚ) : ℚ := if x ≥ 0 then 1 else -1

/-- Predicted label for an input -/
def predict {n : ℕ} (p : Perceptron n) (x : Fin n → ℚ) : ℚ :=
  sign (dot p.weights (augment x))

def correct? {n : ℕ} (p : Perceptron n) (dp : DataPoint n) : Bool :=
  predict p dp.features == dp.label

/-- Update rule: w' = w + y * x_aug when misclassified -/
def update {n : ℕ} (p : Perceptron n) (dp : DataPoint n) : Perceptron n :=
  { weights := fun i => p.weights i + dp.label * augment dp.features i }

abbrev Dataset (n : ℕ) := List (DataPoint n)

def ValidLabel (y : ℚ) : Prop := y = 1 ∨ y = -1
def ValidLabels {n : ℕ} (data : Dataset n) : Prop :=
  ∀ dp ∈ data, ValidLabel dp.label

theorem ValidLabel.sq_eq_one {y : ℚ} (h : ValidLabel y) : y ^ 2 = 1 := by
  cases h with
  | inl h => simp [h]
  | inr h => simp [h]

/-- The margin of a weight vector on a data point: y * (w · x_aug) -/
def margin {n : ℕ} (w : Fin (n + 1) → ℚ) (dp : DataPoint n) : ℚ :=
  dp.label * dot w (augment dp.features)

/-- A dataset is linearly separable with margin γ if ∃ w* s.t. all points have margin at least γ -/
def Separable {n : ℕ} (data : Dataset n) (γ : ℚ) : Prop :=
  ∃ wStar : Fin (n + 1) → ℚ, normSq wStar = 1 ∧ γ > 0 ∧ ∀ dp ∈ data, margin wStar dp ≥ γ

def maxNormSq {n : ℕ} (data : Dataset n) : ℚ :=
  data.foldl (fun acc dp => max acc (normSq (augment dp.features))) 0

def zeroVec (n : ℕ) : Fin n → ℚ := fun _ => 0
