import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

import Perceptron.Definitions
import Perceptron.Basic

open BigOperators Finset

/- Simple helper lemmmas -/

namespace Perceptron

theorem dot_zero_left {n : ℕ} (v : Fin n → ℚ) : dot (zero_vec n) v = 0 := by simp [dot, zero_vec]
theorem norm_sq_zero {n : ℕ} : norm_sq (zero_vec n) = 0 := by simp [norm_sq, zero_vec]
theorem dot_comm {n : ℕ} (v w : Fin n → ℚ) : dot v w = dot w v := by simp [dot, mul_comm]

/-- The dot product after a weight update = the previous dot + the contribution from the update -/
theorem dot_update_weights {n : ℕ}
  (w : Fin (n + 1) → ℚ) (p : LabeledPoint n) (u : Fin (n + 1) → ℚ) :
    dot (fun i => w i + p.label * augment p.features i) u =
    dot w u + p.label * dot (augment p.features) u := by
  simp [dot, Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [add_mul]
  rw [Finset.sum_add_distrib]
  grind

/-- The square norm after a weight update = the previous norm + the contribution from the update -/
theorem norm_sq_update_weights {n : ℕ} (w : Fin (n + 1) → ℚ) (p : LabeledPoint n)
    (hlabel : p.label ^ 2 = 1) :
    norm_sq (fun i => w i + p.label * augment p.features i) =
    norm_sq w + 2 * p.label * dot w (augment p.features) + norm_sq (augment p.features) := by
  simp [norm_sq, dot, Finset.mul_sum]
  rw [←Finset.sum_add_distrib, ←Finset.sum_add_distrib]
  grind

/-- Square norm is nonnegative -/
lemma norm_sq_nonneg {n : ℕ} (v : Fin n → ℚ) : 0 ≤ norm_sq v := by
  apply Finset.sum_nonneg
  intro _ _
  exact sq_nonneg _

/- Convergence -/

/-- Each update increases alignment by at least γ -/
theorem update_alignment {n : ℕ} (wStar : Fin (n + 1) → ℚ) (γ : ℚ)
    (points : List (LabeledPoint n))
    (hmargin : ∀ p ∈ points, margin wStar p ≥ γ)
    (w : Fin (n + 1) → ℚ) (base : ℚ) (hbase : dot w wStar ≥ base) :
    dot (points.foldl (fun w p => fun i => w i + p.label * augment p.features i) w)
    wStar ≥ base + points.length * γ := by
  induction points generalizing w base with
  | nil =>
    simp
    exact hbase
  | cons p rest ih =>
    simp
    have hmargin' : margin wStar p ≥ γ := hmargin p List.mem_cons_self
    have hrest : ∀ p' ∈ rest, margin wStar p' ≥ γ :=
      fun p' h => hmargin p' (List.mem_cons_of_mem p h)
    have hupdate : dot (fun i => w i + p.label * augment p.features i) wStar ≥ base + γ := by
      rw [dot_update_weights]
      rw [margin, dot_comm] at hmargin'
      grind
    grind

/-- After t updates on points with margin ≥ γ, alignment with w* is at least t * γ -/
theorem alignment_after_updates {n : ℕ} (wStar : Fin (n + 1) → ℚ) (γ : ℚ)
    (points : List (LabeledPoint n))
    (hmargin : ∀ p ∈ points, margin wStar p ≥ γ) :
    dot (points.foldl (fun w p => fun i => w i + p.label * augment p.features i)
    (zero_vec (n + 1))) wStar ≥ points.length * γ := by
  have h := update_alignment wStar γ points hmargin (zero_vec (n + 1)) 0 (by simp [dot_zero_left])
  grind

/- Update -/

/-- A point is misclassified by weight vector w if y(w·x_aug) ≤ 0 -/
def misclassified {n : ℕ} (w : Fin (n + 1) → ℚ) (point : LabeledPoint n) : Prop :=
  point.label * dot w (augment point.features) ≤ 0

/-- Single update norm bound: if misclassified, ‖w'‖² ≤ ‖w‖² + ‖x_aug‖² -/
theorem norm_sq_update_misclassified {n : ℕ} (w : Fin (n + 1) → ℚ) (p : LabeledPoint n)
    (hlabel : valid_label p.label) (hmis : misclassified w p) :
    norm_sq (fun i => w i + p.label * augment p.features i) ≤
    norm_sq w + norm_sq (augment p.features) := by
  rw [norm_sq_update_weights w p (valid_label.sq_eq_one hlabel)]
  rw [misclassified] at hmis
  simp
  linarith

/-- An update sequence where each update was on a misclassified point -/
inductive ValidUpdateSeq {n : ℕ} :
  (Fin (n + 1) → ℚ) → List (LabeledPoint n) → (Fin (n + 1) → ℚ) → Prop where
  | nil : ∀ w, ValidUpdateSeq w [] w
  | cons : ∀ w p rest w_final,
      misclassified w p →
      ValidUpdateSeq (fun i => w i + p.label * augment p.features i) rest w_final →
      ValidUpdateSeq w (p :: rest) w_final

/-- The final weight vector from a valid update sequence -/
theorem valid_update_seq_final {n : ℕ} (w : Fin (n + 1) → ℚ) (points : List (LabeledPoint n))
    (w_final : Fin (n + 1) → ℚ) (hseq : ValidUpdateSeq w points w_final) :
    w_final = points.foldl (fun w p => fun i => w i + p.label * augment p.features i) w := by
  induction hseq with
  | nil w => rfl
  | cons w p rest wfinal hmis hrest ih =>
    simp [List.foldl_cons]
    exact ih

/-- Norm bound for valid update sequences -/
theorem norm_bound_valid_seq {n : ℕ} (R_sq : ℚ)
    (w : Fin (n + 1) → ℚ) (points : List (LabeledPoint n)) (w_final : Fin (n + 1) → ℚ)
    (hseq : ValidUpdateSeq w points w_final)
    (hbound : ∀ p ∈ points, norm_sq (augment p.features) ≤ R_sq)
    (hlabels : ∀ p ∈ points, valid_label p.label)
    (B : ℚ) (hB : norm_sq w ≤ B) :
    norm_sq w_final ≤ B + points.length * R_sq := by
  induction hseq generalizing B with
  | nil w =>
    simp
    exact hB
  | cons w p rest w_final hmis hrest ih =>
    simp
    have hbound_point : norm_sq (augment p.features) ≤ R_sq := hbound p List.mem_cons_self
    have hlabel_point : valid_label p.label := hlabels p List.mem_cons_self
    have hbound_rest : ∀ p' ∈ rest, norm_sq (augment p'.features) ≤ R_sq :=
      fun p' h => hbound p' (List.mem_cons_of_mem p h)
    have hlabels_rest : ∀ p' ∈ rest, valid_label p'.label :=
      fun p' h => hlabels p' (List.mem_cons_of_mem p h)
    have h_one_step : norm_sq (fun i => w i + p.label * augment p.features i) ≤ B + R_sq := by
      have := norm_sq_update_misclassified w p hlabel_point hmis
      linarith
    have := ih hbound_rest hlabels_rest (B + R_sq) h_one_step
    linarith

/-- Norm bound starting from zero -/
theorem norm_after_valid_updates {n : ℕ} (R_sq : ℚ)
    (points : List (LabeledPoint n)) (w_final : Fin (n + 1) → ℚ)
    (hseq : ValidUpdateSeq (zero_vec (n + 1)) points w_final)
    (hbound : ∀ p ∈ points, norm_sq (augment p.features) ≤ R_sq)
    (hlabels : ∀ p ∈ points, valid_label p.label) :
    norm_sq w_final ≤ points.length * R_sq := by
  have h := norm_bound_valid_seq R_sq (zero_vec (n + 1)) points w_final hseq hbound hlabels 0
    (by simp [norm_sq_zero])
  linarith

/- Cauchy-Schwarz Inequality: (v · w)² ≤ ‖v‖² * ‖w‖² -/
theorem cauchy_schwarz {n : ℕ} (v w : Fin n → ℚ) :
    (dot v w) ^ 2 ≤ norm_sq v * norm_sq w := by
  by_cases hw : norm_sq w = 0
  · -- case ‖w‖² = 0 ⇒ w = 0
    have hwzero : ∀ i, w i = 0 := by
      intro i
      have hi : (w i) ^ 2 ≤ norm_sq w :=
        Finset.single_le_sum
          (fun j _ => sq_nonneg (w j))
          (Finset.mem_univ i)
      -- from hi and hw we get (w i)² ≤ 0; together with (w i)² ≥ 0,
      -- nlinarith deduces w i = 0
      nlinarith [sq_nonneg (w i)]
    -- if w = 0 then dot v w = 0, so both sides are 0
    simp [dot, hwzero, hw]
  · -- main case: ‖w‖² ≠ 0
    have quad_nonneg : ∀ t : ℚ,
      0 ≤ norm_sq v - 2 * t * dot v w + t ^ 2 * norm_sq w := by
      intro t
      -- 0 ≤ ‖v - t·w‖²
      have h := norm_sq_nonneg (fun i => v i - t * w i)
      have expand :
        norm_sq (fun i => v i - t * w i) =
          norm_sq v - 2 * t * dot v w + t ^ 2 * norm_sq w := by
        simp [norm_sq, dot, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro _ _
        ring
      simpa [expand] using h
    -- evaluate the quadratic at t = ⟨v,w⟩ / ‖w‖²
    have h0 := quad_nonneg (dot v w / norm_sq w)
    have h1 :
      norm_sq v
        - 2 * (dot v w / norm_sq w) * dot v w
        + (dot v w / norm_sq w) ^ 2 * norm_sq w
        = norm_sq v - (dot v w) ^ 2 / norm_sq w := by
      field_simp [pow_two, hw]
      ring
    have h2 : 0 ≤ norm_sq v - (dot v w) ^ 2 / norm_sq w := by
      simpa [h1] using h0
    -- from 0 ≤ ‖v‖² - (⟨v,w⟩² / ‖w‖²) we get ⟨v,w⟩² / ‖w‖² ≤ ‖v‖²
    have step : (dot v w) ^ 2 / norm_sq w ≤ norm_sq v := by
      linarith
    -- multiply both sides by ‖w‖² ≥ 0
    have h3 :=
      mul_le_mul_of_nonneg_right step (norm_sq_nonneg w)
    -- rewrite the left-hand side
    have h4 :
      (dot v w) ^ 2 = (dot v w) ^ 2 / norm_sq w * norm_sq w := by
      field_simp [hw]
    have h5 : (dot v w) ^ 2 ≤ norm_sq v * norm_sq w := by
      simpa [h4.symm] using h3
    exact h5

/-- Perceptron Convergence Theorem: Number of updates is bounded by R²/γ² -/
theorem perceptron_convergence {n : ℕ} (data : List (LabeledPoint n)) (γ R_sq : ℚ)
    (hγ_pos : γ > 0) (hR_pos : R_sq > 0)
    (hsep : separable data γ)
    (hbound : ∀ p ∈ data, norm_sq (augment p.features) ≤ R_sq)
    (hlabels : valid_labels data) :
    ∀ (updates : List (LabeledPoint n)) (w_final : Fin (n + 1) → ℚ),
      (∀ p ∈ updates, p ∈ data) →
      ValidUpdateSeq (zero_vec (n + 1)) updates w_final →
      updates.length ≤ R_sq / (γ ^ 2) := by

  intro updates w_final hsubset hseq
  rcases hsep with ⟨wStar, hwStar_norm, _, hwStar_margin⟩

  -- unfold the final weight
  have hw_eq :
      w_final =
        updates.foldl
          (fun w p => fun i => w i + p.label * augment p.features i)
          (zero_vec (n + 1)) :=
    valid_update_seq_final (zero_vec (n + 1)) updates w_final hseq

  -- alignment lower bound: ⟨w_final, w*⟩ ≥ (#updates) * γ
  have h_align : dot w_final wStar ≥ updates.length * γ := by
    rw [hw_eq]
    exact
      alignment_after_updates wStar γ updates
        (fun p hp => hwStar_margin p (hsubset p hp))

  -- norm upper bound: ‖w_final‖² ≤ (#updates) * R²
  have h_norm : norm_sq w_final ≤ updates.length * R_sq :=
    norm_after_valid_updates R_sq updates w_final hseq
      (fun p hp => hbound p (hsubset p hp))
      (fun p hp => hlabels p (hsubset p hp))

  -- Cauchy–Schwarz with ‖w*‖² = 1 ⇒ ⟨w_final, w*⟩² ≤ ‖w_final‖²
  have h_cs : (dot w_final wStar) ^ 2 ≤ norm_sq w_final := by
    have h := cauchy_schwarz w_final wStar
    -- hwStar_norm : norm_sq wStar = 1
    simpa [hwStar_norm, mul_comm] using h

  -- combine: ((#updates) * γ)² ≤ (#updates) * R²
  have h2 : (updates.length * γ) ^ 2 ≤ updates.length * R_sq := by
    -- square the alignment inequality
    have h_nonneg : 0 ≤ (updates.length : ℚ) * γ := by
      have hlen : 0 ≤ (updates.length : ℚ) := by simp
      exact mul_nonneg hlen (le_of_lt hγ_pos)
    have h1' := mul_self_le_mul_self h_nonneg h_align
    have h1 : (updates.length * γ) ^ 2 ≤ (dot w_final wStar) ^ 2 := by
      simpa [pow_two]
    calc
      (updates.length * γ) ^ 2 ≤ (dot w_final wStar) ^ 2 := h1
      _                        ≤ norm_sq w_final := h_cs
      _                        ≤ updates.length * R_sq := h_norm

  by_cases ht : updates.length = 0
  · -- no updates: goal is 0 ≤ R² / γ²
    simp [ht]
    positivity
  · have ht_pos : 0 < (updates.length : ℚ) := by positivity

    -- rewrite h2 as t * (t * γ²) ≤ t * R² and cancel positive t
    have htmp :
        (updates.length : ℚ) * ((updates.length : ℚ) * γ ^ 2)
          ≤ (updates.length : ℚ) * R_sq := by
      -- (t * γ)² = t² * γ² = t * (t * γ²)
      simpa [pow_two, mul_left_comm, mul_assoc] using h2

    -- cancel the positive factor
    have h3 : (updates.length : ℚ) * γ ^ 2 ≤ R_sq := le_of_mul_le_mul_left htmp ht_pos

    have h4 : (updates.length : ℚ) ≤ R_sq / γ ^ 2 := by
      field_simp
      exact h3

    exact h4

end Perceptron
