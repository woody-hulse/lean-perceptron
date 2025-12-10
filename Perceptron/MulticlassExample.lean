import Perceptron.Multiclass

set_option linter.style.nativeDecide false
set_option maxRecDepth 1000

namespace MultiClassPerceptron

def small_mnist_data : List (LabeledPoint mnist_num_features) := mnist_data.take 10

#eval do
  -- Train multiclass model
  let trained_state : State mnist_num_classes mnist_num_features :=
    train (num_classes := mnist_num_classes) small_mnist_data
  IO.println "Training completed."

  -- Convergence steps per class
  IO.println "Convergence steps per class:"
  let convergences := show_convergences trained_state
  convergences.forM IO.println

  -- Show predictions
  show_predictions mnist_num_features small_mnist_data trained_state

  -- Show accuracy
  let correct_counts :=
    (List.finRange mnist_num_classes).map fun cls =>
      let ts := trained_state.states cls
      let binary_data := to_one_vs_all (num_classes := mnist_num_classes) small_mnist_data cls
      let correct :=
        binary_data.filter (fun dp => Perceptron.correct? ts.perceptron dp) |>.length
      (cls.val, correct, binary_data.length)
  IO.println "Accuracy per class (correct / total):"
  correct_counts.forM fun (cls, correct, total) =>
    IO.println s!"  Class {cls}: {correct} / {total}"

  -- Show weights
  IO.println "Perceptron weights:"
  (List.finRange mnist_num_classes).forM fun cls => do
    let ts := trained_state.states cls
    let weights := weights_to_list ts.perceptron.weights
    IO.println s!"  Perceptron {cls.val}: {weights}"


/-
abbrev mnist_num_classes := 10
def small_binarized_mnist_data : List (LabeledPoint 784) :=
  to_one_vs_all (num_classes := mnist_num_classes) small_mnist_data 0

def min_margin {n : ℕ} (w_star : Fin (n + 1) → ℚ) (data : List (LabeledPoint n)) : ℚ :=
  match data with
  | [] => 0
  | dp :: rest => rest.foldl (fun acc dp => min acc (margin w_star dp)) (margin w_star dp)

def find_w_star {n : ℕ} (data : List (LabeledPoint n)) (maxIter : ℕ := 1000) : Fin (n + 1) → ℚ :=
  (Perceptron.train_until_convergence data maxIter).perceptron.weights

-- w* = (3/5, 4/5, 0), ||w*||² = 9/25 + 16/25 = 1

def w_star : Fin 785 → ℚ := fun i => List.getD w_star_list i.val 0

def R_sq : ℚ := max_norm_sq small_mnist_data
def γ : ℚ := min_margin w_star small_mnist_data

#eval R_sq
#eval γ

theorem R_sq_pos : R_sq > 0 := by native_decide

theorem mnist_data_norm_bound : ∀ dp ∈ mnist_data, norm_sq (augment dp.features) ≤ R_sq := by
  intro dp hdp
  fin_cases hdp <;> native_decide

theorem γ_pos : γ > 0 := by native_decide

theorem w_star_norm : norm_sq w_star = 1 := by
  simp only [norm_sq, w_star, Fin.sum_univ_three]
  native_decide

theorem margin_w_star_ge_γ : ∀ dp ∈ mnist_data, margin w_star dp ≥ γ := by
  intro dp hdp
  fin_cases hdp <;> native_decide

theorem mnist_data_separable : separable mnist_data γ := by
  rw [separable]
  exact ⟨w_star, w_star_norm, γ_pos, margin_w_star_ge_γ⟩

theorem mnist_data_valid_labels : valid_labels mnist_data := by
  intro dp hdp
  rw [valid_label]
  fin_cases hdp <;> native_decide

theorem mnist_data_convergence :
    ∀ (updates : List (LabeledPoint 2)) (w_final : Fin 3 → ℚ),
      (∀ dp ∈ updates, dp ∈ small_mnist_data) →
      ValidUpdateSeq (zero_vec 3) updates w_final →
      updates.length ≤ R_sq / (γ ^ 2) := by
  exact perceptron_convergence small_mnist_data γ R_sq γ_pos R_sq_pos
        mnist_data_separable mnist_data_norm_bound mnist_data_valid_labels

-- Bound on the number of updates
#eval (R_sq / γ^2 : ℚ)

#eval
  let result := train_until_convergence small_mnist_data 100
  let p := result.perceptron
  let correct := all_correct? p small_mnist_data
  (s!"Updates: {result.num_updates}",
   s!"Converged: {correct}",
   s!"Bound: {R_sq / γ^2}",
   s!"Weights: ({p.weights 0}, {p.weights 1}, {p.weights 2})")

-/

end MultiClassPerceptron
