import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

import Perceptron.Definitions
import Perceptron.Basic
import Perceptron.Data
import Perceptron.Proofs

open BigOperators Finset

namespace MultiClassPerceptron

structure T (num_classes num_features : ℕ) where
  perceptrons : Fin num_classes → Perceptron.T num_features

structure State (num_classes num_features : ℕ) where
  states : Fin num_classes → Perceptron.State num_features

/-- Given a list of LabeledPoints with n classes, turn it into n binary classification problems -/
def to_one_vs_all {num_classes num_features : ℕ} (data : List (LabeledPoint num_features)) :
    Fin num_classes → List (LabeledPoint num_features) :=
  fun cls =>
    data.filterMap fun dp =>
      if dp.label = (cls.val : ℚ) then
        some { features := dp.features, label := 1 }
      else
        some { features := dp.features, label := -1 }

def init_state (num_classes num_features) : State num_classes num_features :=
  { states := fun _ => Perceptron.init_state num_features }

/- Train each binary perceptron on its corresponding data -/
def train {num_classes num_features : ℕ}
    (data : List (LabeledPoint num_features)) (max_iter : ℕ := 100)
    : State num_classes num_features :=
  let one_vs_all_data := to_one_vs_all (num_classes := num_classes) data
  let state := init_state num_classes num_features
  (List.finRange num_classes).foldl
    (fun state cls =>
      let binary_data := one_vs_all_data cls
      let trained_state := Perceptron.train_until_convergence binary_data max_iter
      let states' :=
        fun c => if c = cls then trained_state else state.states c
      { states := states' })
    state

def show_weights {num_classes num_features : ℕ}
  (mcp : T num_classes num_features)
  (cls : Fin num_classes) (feature : Fin (num_features + 1)) : ℚ :=
  (mcp.perceptrons cls).weights feature

def weights_to_list {n : Nat} (w : Fin n → ℚ) : List ℚ :=
  (List.finRange n).map (fun i => w i)

def show_convergences {num_classes num_features : ℕ}
    (state : State num_classes num_features) : List String :=
  (List.finRange num_classes).map fun cls =>
    let ts := state.states cls
    s!"  Class {cls.val}: {ts.num_updates} updates"

def predict {num_classes num_features : ℕ}
    (state : State num_classes num_features)
    (x : Fin num_features → ℚ) : List ℚ :=
  (List.finRange num_classes).map fun cls =>
    let ts := state.states cls
    let p  := Perceptron.predict ts.perceptron x
    sign p

def show_predictions (n : ℕ) (data : List (LabeledPoint n))
    (state : State 10 n) : IO Unit :=
  data.forM fun dp => do
    let preds := predict state dp.features
    IO.println s!"Predictions: {preds}"
    show_labeled_point dp 28 170 |> IO.println

end MultiClassPerceptron
