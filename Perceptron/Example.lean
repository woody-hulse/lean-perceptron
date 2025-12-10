import Perceptron.Basic
import Perceptron.Proofs

set_option linter.style.nativeDecide false

namespace Perceptron

-- Example data
def example_data : List (LabeledPoint 2) := [
  { features := ![3, 4], label := 1 },     -- margin with (3,4,0)/5: (9+16)/5 = 5
  { features := ![6, 8], label := 1 },     -- margin: (18+32)/5 = 10
  { features := ![-3, -4], label := -1 },  -- margin: (-1)*(-9-16)/5 = 5
  { features := ![-6, -8], label := -1 }   -- margin: (-1)*(-18-32)/5 = 10
]

/- Compute properties of data -/

def min_margin {n : ℕ} (wStar : Fin (n + 1) → ℚ) (data : List (LabeledPoint n)) : ℚ :=
  match data with
  | [] => 0
  | dp :: rest => rest.foldl (fun acc dp => min acc (margin wStar dp)) (margin wStar dp)

-- w* = (3/5, 4/5, 0), ||w*||² = 9/25 + 16/25 = 1
def w_star : Fin 3 → ℚ := ![3/5, 4/5, 0]

def R_sq : ℚ := max_norm_sq example_data
def γ : ℚ := min_margin w_star example_data

#eval R_sq
#eval γ

theorem R_sq_pos : R_sq > 0 := by native_decide

theorem example_data_norm_bound : ∀ dp ∈ example_data, norm_sq (augment dp.features) ≤ R_sq := by
  intro dp hdp
  fin_cases hdp <;> native_decide

theorem γ_pos : γ > 0 := by native_decide

theorem w_star_norm : norm_sq w_star = 1 := by
  simp only [norm_sq, w_star, Fin.sum_univ_three]
  native_decide

theorem margin_w_star_ge_γ : ∀ dp ∈ example_data, margin w_star dp ≥ γ := by
  intro dp hdp
  fin_cases hdp <;> native_decide

theorem example_data_separable : separable example_data γ := by
  rw [separable]
  exact ⟨w_star, w_star_norm, γ_pos, margin_w_star_ge_γ⟩

theorem example_data_valid_labels : valid_labels example_data := by
  intro dp hdp
  rw [valid_label]
  fin_cases hdp <;> native_decide

theorem example_data_convergence :
    ∀ (updates : List (LabeledPoint 2)) (w_final : Fin 3 → ℚ),
      (∀ dp ∈ updates, dp ∈ example_data) →
      ValidUpdateSeq (zero_vec 3) updates w_final →
      updates.length ≤ R_sq / (γ ^ 2) := by
  exact perceptron_convergence example_data γ R_sq γ_pos R_sq_pos
        example_data_separable example_data_norm_bound example_data_valid_labels

-- Bound on the number of updates
#eval (R_sq / γ^2 : ℚ)

#eval
  let result := train_until_convergence example_data 100
  let p := result.perceptron
  let correct := all_correct? p example_data
  (s!"Updates: {result.num_updates}",
   s!"Converged: {correct}",
   s!"Bound: {R_sq / γ^2}",
   s!"Weights: ({p.weights 0}, {p.weights 1}, {p.weights 2})")

end Perceptron
