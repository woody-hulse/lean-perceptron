import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

import Perceptron.Basic
import Perceptron.Data
import Perceptron.Loader

open BigOperators Finset

structure MultiClassPerceptron (nClasses nFeatures : ℕ) where
  perceptrons : Fin nClasses → Perceptron nFeatures

/-- Given a dataset with multiple classes, turn it into n binary classification probelms -/
def toOneVsAll {nClasses nFeatures : ℕ} (data : Dataset nFeatures) :
    Fin nClasses → Dataset nFeatures :=
  fun cls =>
    data.filterMap fun dp =>
      if dp.label = (cls.val : ℚ) then
        some { features := dp.features, label := 1 }
      else
        some { features := dp.features, label := -1 }

structure mcTrainState (nClasses nFeatures : ℕ) where
  states : Fin nClasses → TrainState nFeatures

def mcInitState (nClasses nFeatures) : mcTrainState nClasses nFeatures :=
  { states := fun _ => initState nFeatures }

/- Train each binary perceptron on its corresponding dataset -/
def mcTrain {nClasses nFeatures : ℕ}
    (data : Dataset nFeatures) (maxIter : ℕ := 100) : mcTrainState nClasses nFeatures :=
  let oneVsAllData := toOneVsAll (nClasses := nClasses) data
  let initialState := mcInitState nClasses nFeatures
  (List.finRange nClasses).foldl
    (fun state cls =>
      let binaryData := oneVsAllData cls
      let trainedState := trainUntilConvergence binaryData maxIter
      let newStates :=
        fun c => if c = cls then trainedState else state.states c
      { states := newStates })
    initialState

def mcShowWeights {nClasses nFeatures : ℕ}
  (mcp : MultiClassPerceptron nClasses nFeatures)
  (cls : Fin nClasses) (feature : Fin (nFeatures + 1)) : ℚ :=
  (mcp.perceptrons cls).weights feature

def weightsToList {n : Nat} (w : Fin n → ℚ) : List ℚ :=
  (List.finRange n).map (fun i => w i)

def showConvergences {nClasses nFeatures : ℕ}
    (state : mcTrainState nClasses nFeatures) : List String :=
  (List.finRange nClasses).map fun cls =>
    let ts := state.states cls
    s!"  Class {cls.val}: {ts.numUpdates} updates"

def mcPredict {nClasses nFeatures : ℕ}
    (state : mcTrainState nClasses nFeatures)
    (x : Fin nFeatures → ℚ) : List ℚ :=
  (List.finRange nClasses).map fun cls =>
    let ts := state.states cls
    let p  := predict ts.perceptron x
    sign p

def showPredictions (n : ℕ) (data : Dataset n)
    (state : mcTrainState 10 n) : IO Unit :=
  data.forM fun dp => do
    let preds := mcPredict state dp.features
    IO.println s!"Predictions: {preds}"
    showDataPoint dp 28 170 |> IO.println

#eval do
  -- Load dataset
  let ⟨nFeatures, data⟩ ← loadCSVDataset "mnist_pruned.csv" 784
  let smallData := data.take 10
  IO.println s!"Loaded dataset with {data.length} samples and {nFeatures} features"

  -- Train multiclass model
  let nClasses := 10
  let trainedState : mcTrainState nClasses nFeatures :=
    mcTrain (nClasses := nClasses) smallData
  IO.println "Training completed."

  -- Convergence steps per class
  IO.println "Convergence steps per class:"
  let convergences := showConvergences trainedState
  convergences.forM IO.println

  -- Show predictions
  showPredictions nFeatures smallData trainedState
