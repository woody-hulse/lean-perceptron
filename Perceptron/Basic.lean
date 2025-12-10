import Perceptron.Definitions

open BigOperators Finset

namespace Perceptron

/-- A perceptron with n input features (n + 1 weights includes the bias term) -/
structure T (n : ℕ) where
  weights : Fin (n + 1) → ℚ

/-- For representing the training state of a perceptron -/
structure State (n : ℕ) where
  perceptron : T n
  num_updates : ℕ

/-- Predicted label for an input -/
def predict {n : ℕ} (p : T n) (x : Fin n → ℚ) : ℚ :=
  sign (dot p.weights (augment x))

def correct? {n : ℕ} (p : T n) (dp : LabeledPoint n) : Bool :=
  predict p dp.features == dp.label

/-- Update rule: w' = w + y * x_aug when misclassified -/
def update {n : ℕ} (p : T n) (dp : LabeledPoint n) : T n :=
  { weights := fun i => p.weights i + dp.label * augment dp.features i }

def init_state (n : ℕ) : State n :=
  { perceptron := { weights := zero_vec (n + 1) }, num_updates := 0 }

def train_step {n : ℕ} (state : State n) (p : LabeledPoint n) : State n :=
  if correct? state.perceptron p then state
  else { perceptron := update state.perceptron p, num_updates := state.num_updates + 1 }

def train_epoch {n : ℕ} (state : State n) (data : List (LabeledPoint n)) : State n :=
  data.foldl train_step state

def all_correct? {n : ℕ} (p : T n) (data : List (LabeledPoint n)) : Bool :=
  data.all (correct? p)

def train_until_convergence {n : ℕ} (data : List (LabeledPoint n)) (maxIter : ℕ) : State n :=
  let rec go (state : State n) (remaining : ℕ) : State n :=
    match remaining with
    | 0 => state
    | k + 1 => if all_correct? state.perceptron data then state else go (train_epoch state data) k
  go (init_state n) maxIter

/- Examples -/

def and_gate_data : List (LabeledPoint 2) := [
  { features := ![0, 0], label := -1 },
  { features := ![0, 1], label := -1 },
  { features := ![1, 0], label := -1 },
  { features := ![1, 1], label := 1 }
]

def or_gate_data : List (LabeledPoint 2) := [
  { features := ![0, 0], label := -1 },
  { features := ![0, 1], label := 1 },
  { features := ![1, 0], label := 1 },
  { features := ![1, 1], label := 1 }
]

def xor_gate_data : List (LabeledPoint 2) := [
  { features := ![0, 0], label := -1 },
  { features := ![0, 1], label := 1 },
  { features := ![1, 0], label := 1 },
  { features := ![1, 1], label := -1 }
]

#eval
  let result := train_until_convergence and_gate_data 100
  let p := result.perceptron
  (p.weights 0, p.weights 1, p.weights 2, result.num_updates, all_correct? p and_gate_data)

#eval
  let result := train_until_convergence or_gate_data 100
  let p := result.perceptron
  (p.weights 0, p.weights 1, p.weights 2, result.num_updates, all_correct? p or_gate_data)

#eval
  let result := train_until_convergence xor_gate_data 100
  let p := result.perceptron
  (p.weights 0, p.weights 1, p.weights 2, result.num_updates, all_correct? p xor_gate_data)

end Perceptron
