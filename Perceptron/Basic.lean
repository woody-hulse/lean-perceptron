import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

import Perceptron.Definitions

open BigOperators Finset

/-! ## Key Lemmas -/

theorem dot_zero_left {n : ℕ} (v : Fin n → ℚ) : dot (zeroVec n) v = 0 := by simp [dot, zeroVec]
theorem normSq_zero {n : ℕ} : normSq (zeroVec n) = 0 := by simp [normSq, zeroVec]
theorem dot_comm {n : ℕ} (v w : Fin n → ℚ) : dot v w = dot w v := by simp [dot, mul_comm]

/-- Helper for dot product after weight update -/
theorem dot_update_weights {n : ℕ} (w : Fin (n + 1) → ℚ) (dp : DataPoint n) (u : Fin (n + 1) → ℚ) :
    dot (fun i => w i + dp.label * augment dp.features i) u =
    dot w u + dp.label * dot (augment dp.features) u := by
  simp only [dot, Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1; apply Finset.sum_congr rfl; intro i _; ring

/-- Helper for normSq after weight update -/
theorem normSq_update_weights {n : ℕ} (w : Fin (n + 1) → ℚ) (dp : DataPoint n)
    (hlabel : dp.label ^ 2 = 1) :
    normSq (fun i => w i + dp.label * augment dp.features i) =
    normSq w + 2 * dp.label * dot w (augment dp.features) + normSq (augment dp.features) := by
  simp only [normSq, dot, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; ring_nf; rw [hlabel, one_mul]

lemma normSq_nonneg {n : ℕ} (v : Fin n → ℚ) : 0 ≤ normSq v := by
  apply Finset.sum_nonneg; intro i _; exact sq_nonneg _

/-! ## Convergence Lemmas -/

/-- Helper lemma for alignment with accumulator -/
theorem alignment_accumulator {n : ℕ} (wStar : Fin (n + 1) → ℚ) (γ : ℚ)
    (points : List (DataPoint n))
    (hmargin : ∀ dp ∈ points, margin wStar dp ≥ γ)
    (w : Fin (n + 1) → ℚ) (base : ℚ) (hbase : dot w wStar ≥ base) :
    dot (points.foldl (fun w dp => fun i => w i + dp.label * augment dp.features i) w) wStar
    ≥ base + points.length * γ := by
  induction points generalizing w base with
  | nil => simp; linarith
  | cons dp rest ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hmarg : margin wStar dp ≥ γ := hmargin dp List.mem_cons_self
    have hrest : ∀ dp' ∈ rest, margin wStar dp' ≥ γ :=
      fun dp' h => hmargin dp' (List.mem_cons_of_mem dp h)
    have h_update : dot (fun i => w i + dp.label * augment dp.features i) wStar ≥ base + γ := by
      rw [dot_update_weights]
      unfold margin at hmarg
      rw [dot_comm] at hmarg
      linarith
    have := ih hrest _ (base + γ) h_update
    linarith

/-- After t updates on points with margin ≥ γ, alignment with w* is at least t * γ -/
theorem alignment_after_updates {n : ℕ} (wStar : Fin (n + 1) → ℚ) (γ : ℚ)
    (points : List (DataPoint n))
    (hmargin : ∀ dp ∈ points, margin wStar dp ≥ γ) :
    dot (points.foldl (fun w dp => fun i => w i + dp.label * augment dp.features i)
         (zeroVec (n + 1))) wStar
    ≥ points.length * γ := by
  have h := alignment_accumulator wStar γ points hmargin (zeroVec (n + 1)) 0
            (by simp [dot_zero_left])
  linarith

/-! ## Misclassification and Valid Update Sequences -/

/-- A point is misclassified by weight vector w if y(w·x_aug) ≤ 0 -/
def Misclassified {n : ℕ} (w : Fin (n + 1) → ℚ) (dp : DataPoint n) : Prop :=
  dp.label * dot w (augment dp.features) ≤ 0

/-- Single update norm bound: if misclassified, ‖w'‖² ≤ ‖w‖² + ‖x_aug‖² -/
theorem normSq_update_misclassified {n : ℕ} (w : Fin (n + 1) → ℚ) (dp : DataPoint n)
    (hlabel : ValidLabel dp.label) (hmis : Misclassified w dp) :
    normSq (fun i => w i + dp.label * augment dp.features i) ≤
    normSq w + normSq (augment dp.features) := by
  rw [normSq_update_weights w dp (ValidLabel.sq_eq_one hlabel)]
  unfold Misclassified at hmis
  linarith

/-- An update sequence where each update was on a misclassified point -/
inductive ValidUpdateSeq {n : ℕ} :
  (Fin (n + 1) → ℚ) → List (DataPoint n) → (Fin (n + 1) → ℚ) → Prop where
  | nil : ∀ w, ValidUpdateSeq w [] w
  | cons : ∀ w dp rest w_final,
      Misclassified w dp →
      ValidUpdateSeq (fun i => w i + dp.label * augment dp.features i) rest w_final →
      ValidUpdateSeq w (dp :: rest) w_final

/-- The final weight vector from a valid update sequence -/
theorem valid_update_seq_final {n : ℕ} (w : Fin (n + 1) → ℚ) (points : List (DataPoint n))
    (w_final : Fin (n + 1) → ℚ) (hseq : ValidUpdateSeq w points w_final) :
    w_final = points.foldl (fun w dp => fun i => w i + dp.label * augment dp.features i) w := by
  induction hseq with
  | nil w => rfl
  | cons w dp rest w_final hmis hrest ih =>
    simp only [List.foldl_cons]
    exact ih

/-- Norm bound for valid update sequences -/
theorem norm_bound_valid_seq {n : ℕ} (R_sq : ℚ)
    (w : Fin (n + 1) → ℚ) (points : List (DataPoint n)) (w_final : Fin (n + 1) → ℚ)
    (hseq : ValidUpdateSeq w points w_final)
    (hbound : ∀ dp ∈ points, normSq (augment dp.features) ≤ R_sq)
    (hlabels : ∀ dp ∈ points, ValidLabel dp.label)
    (B : ℚ) (hB : normSq w ≤ B) :
    normSq w_final ≤ B + points.length * R_sq := by
  induction hseq generalizing B with
  | nil w => simp; linarith
  | cons w dp rest w_final hmis hrest ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    have hbound_dp : normSq (augment dp.features) ≤ R_sq := hbound dp List.mem_cons_self
    have hlabel_dp : ValidLabel dp.label := hlabels dp List.mem_cons_self
    have hbound_rest : ∀ dp' ∈ rest, normSq (augment dp'.features) ≤ R_sq :=
      fun dp' h => hbound dp' (List.mem_cons_of_mem dp h)
    have hlabels_rest : ∀ dp' ∈ rest, ValidLabel dp'.label :=
      fun dp' h => hlabels dp' (List.mem_cons_of_mem dp h)
    have h_one_step : normSq (fun i => w i + dp.label * augment dp.features i) ≤ B + R_sq := by
      have := normSq_update_misclassified w dp hlabel_dp hmis
      linarith
    have := ih hbound_rest hlabels_rest (B + R_sq) h_one_step
    linarith

/-- Norm bound starting from zero -/
theorem norm_after_valid_updates {n : ℕ} (R_sq : ℚ)
    (points : List (DataPoint n)) (w_final : Fin (n + 1) → ℚ)
    (hseq : ValidUpdateSeq (zeroVec (n + 1)) points w_final)
    (hbound : ∀ dp ∈ points, normSq (augment dp.features) ≤ R_sq)
    (hlabels : ∀ dp ∈ points, ValidLabel dp.label) :
    normSq w_final ≤ points.length * R_sq := by
  have h := norm_bound_valid_seq R_sq (zeroVec (n + 1)) points w_final hseq hbound hlabels 0
            (by simp [normSq_zero])
  linarith

/-! ## Cauchy-Schwarz -/

theorem cauchy_schwarz {n : ℕ} (v w : Fin n → ℚ) :
    (dot v w) ^ 2 ≤ normSq v * normSq w := by
  by_cases hw : normSq w = 0
  · have hw_zero : ∀ i, w i = 0 := by
      intro i
      have hi : (w i) ^ 2 ≤ normSq w :=
        Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
      simp only [hw] at hi; nlinarith [sq_nonneg (w i)]
    simp only [dot, hw_zero, mul_zero, Finset.sum_const_zero, ne_eq, OfNat.ofNat_ne_zero,
               not_false_eq_true, zero_pow, hw, mul_zero, le_refl]
  · have hw_pos : normSq w > 0 := (normSq_nonneg w).lt_of_ne' hw
    have key : ∀ t : ℚ, 0 ≤ normSq v - 2 * t * dot v w + t ^ 2 * normSq w := by
      intro t
      have expand : normSq (fun i => v i - t * w i) =
                    normSq v - 2 * t * dot v w + t ^ 2 * normSq w := by
        simp only [normSq, dot, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [← expand]; exact normSq_nonneg _
    specialize key (dot v w / normSq w)
    have : normSq v - 2 * (dot v w / normSq w) * dot v w +
           (dot v w / normSq w) ^ 2 * normSq w = normSq v - (dot v w) ^ 2 / normSq w := by
      field_simp; ring
    rw [this] at key
    have step : (dot v w) ^ 2 / normSq w ≤ normSq v := by linarith
    calc (dot v w) ^ 2 = (dot v w) ^ 2 / normSq w * normSq w := by field_simp
      _ ≤ normSq v * normSq w := mul_le_mul_of_nonneg_right step (le_of_lt hw_pos)

/-! ## Main Convergence Theorem -/

theorem perceptron_convergence {n : ℕ} (data : Dataset n) (γ R_sq : ℚ)
    (hγ_pos : γ > 0) (hR_pos : R_sq > 0)
    (hsep : Separable data γ)
    (hbound : ∀ dp ∈ data, normSq (augment dp.features) ≤ R_sq)
    (hlabels : ValidLabels data) :
    ∀ (updates : List (DataPoint n)) (w_final : Fin (n + 1) → ℚ),
      (∀ dp ∈ updates, dp ∈ data) →
      ValidUpdateSeq (zeroVec (n + 1)) updates w_final →
      updates.length ≤ R_sq / (γ ^ 2) := by
  intro updates w_final hsubset hseq
  obtain ⟨wStar, hwStar_norm, _, hwStar_margin⟩ := hsep
  have hw_eq : w_final = updates.foldl (fun w dp => fun i => w i + dp.label * augment dp.features i)
               (zeroVec (n + 1)) := valid_update_seq_final (zeroVec (n + 1)) updates w_final hseq
  have h_align : dot w_final wStar ≥ updates.length * γ := by
    rw [hw_eq]
    exact alignment_after_updates wStar γ updates (fun dp hdp => hwStar_margin dp (hsubset dp hdp))
  have h_norm : normSq w_final ≤ updates.length * R_sq :=
    norm_after_valid_updates R_sq updates w_final hseq
      (fun dp hdp => hbound dp (hsubset dp hdp))
      (fun dp hdp => hlabels dp (hsubset dp hdp))
  have h_cs : (dot w_final wStar) ^ 2 ≤ normSq w_final := by
    have := cauchy_schwarz w_final wStar
    rw [hwStar_norm, mul_one] at this
    exact this
  have h1 : (updates.length * γ) ^ 2 ≤ (dot w_final wStar) ^ 2 := by
    rw [sq, sq]
    apply mul_self_le_mul_self (by positivity) h_align
  have h2 : (updates.length * γ) ^ 2 ≤ updates.length * R_sq := calc
    (updates.length * γ) ^ 2 ≤ (dot w_final wStar) ^ 2 := h1
    _ ≤ normSq w_final := h_cs
    _ ≤ updates.length * R_sq := h_norm
  by_cases ht : updates.length = 0
  · simp [ht]; positivity
  · have ht_pos : (updates.length : ℚ) > 0 := by simp only [Nat.cast_pos]; omega
    have h3 : (updates.length : ℚ) * γ ^ 2 ≤ R_sq := by
      have : (updates.length : ℚ) ^ 2 * γ ^ 2 ≤ updates.length * R_sq := by
        calc _ = (updates.length * γ) ^ 2 := by ring
          _ ≤ updates.length * R_sq := h2
      have := div_le_div_of_nonneg_right this (le_of_lt (sq_pos_of_pos hγ_pos))
      field_simp at this; linarith
    calc (updates.length : ℚ) = updates.length * γ ^ 2 / γ ^ 2 := by field_simp
      _ ≤ R_sq / γ ^ 2 := div_le_div_of_nonneg_right h3 (le_of_lt (sq_pos_of_pos hγ_pos))

/-! ## Training Implementation -/

structure TrainState (n : ℕ) where
  perceptron : Perceptron n
  numUpdates : ℕ

def initState (n : ℕ) : TrainState n :=
  { perceptron := { weights := zeroVec (n + 1) }, numUpdates := 0 }

def trainStep {n : ℕ} (state : TrainState n) (dp : DataPoint n) : TrainState n :=
  if correct? state.perceptron dp then state
  else { perceptron := update state.perceptron dp, numUpdates := state.numUpdates + 1 }

def trainEpoch {n : ℕ} (state : TrainState n) (data : Dataset n) : TrainState n :=
  data.foldl trainStep state

def allCorrect {n : ℕ} (p : Perceptron n) (data : Dataset n) : Bool :=
  data.all (correct? p)

def trainUntilConvergence {n : ℕ} (data : Dataset n) (maxIter : ℕ) : TrainState n :=
  let rec go (state : TrainState n) (remaining : ℕ) : TrainState n :=
    match remaining with
    | 0 => state
    | k + 1 => if allCorrect state.perceptron data then state else go (trainEpoch state data) k
  go (initState n) maxIter

/-! ## Connecting Training to Convergence -/

/-- When correct? returns false, the point is misclassified -/
theorem not_correct_implies_misclassified {n : ℕ} (p : Perceptron n) (dp : DataPoint n)
    (hlabel : ValidLabel dp.label) (h : correct? p dp = false) :
    Misclassified p.weights dp := by
  unfold correct? predict sign at h
  unfold Misclassified
  simp only [beq_eq_false_iff_ne, ne_eq] at h
  cases hlabel with
  | inl hy =>
    -- dp.label = 1, so we need dot w x_aug ≤ 0
    simp only [hy, one_mul] at h ⊢
    by_contra hcon
    push_neg at hcon
    -- hcon : dot p.weights (augment dp.features) > 0
    have hge : dot p.weights (augment dp.features) ≥ 0 := le_of_lt hcon
    -- h : ¬(if dot ... ≥ 0 then 1 else -1) = 1
    -- with hge, the if is true, so this is ¬(1 = 1) = False
    rw [if_pos hge] at h
    exact h rfl
  | inr hy =>
    simp only [hy] at h ⊢
    by_contra hcon
    simp only [neg_one_mul] at hcon
    push_neg at hcon
    -- hcon : 0 < -dot p.weights (augment dp.features)
    -- This means dot p.weights (augment dp.features) < 0
    have hlt : dot p.weights (augment dp.features) < 0 := neg_pos.mp hcon
    have hlt' : ¬ dot p.weights (augment dp.features) ≥ 0 := not_le.mpr hlt
    -- h : ¬(if dot ... ≥ 0 then 1 else -1) = -1
    -- with hlt', the if is false, so this is ¬((-1) = -1) = False
    rw [if_neg hlt'] at h
    exact h rfl

/-- Compute the theoretical bound on number of updates -/
def convergenceBound (γ R_sq : ℚ) : ℕ := Nat.ceil (R_sq / γ ^ 2)

/-! ## Examples -/

def andGateData : Dataset 2 := [
  { features := ![0, 0], label := -1 },
  { features := ![0, 1], label := -1 },
  { features := ![1, 0], label := -1 },
  { features := ![1, 1], label := 1 }
]

def orGateData : Dataset 2 := [
  { features := ![0, 0], label := -1 },
  { features := ![0, 1], label := 1 },
  { features := ![1, 0], label := 1 },
  { features := ![1, 1], label := 1 }
]

#eval
  let result := trainUntilConvergence andGateData 100
  let p := result.perceptron
  -- weights are now (w0, w1, bias)
  (p.weights 0, p.weights 1, p.weights 2, result.numUpdates, allCorrect p andGateData)

#eval
  let result := trainUntilConvergence orGateData 100
  let p := result.perceptron
  (p.weights 0, p.weights 1, p.weights 2, result.numUpdates, allCorrect p orGateData)

-- Compute max ‖x_aug‖² for AND gate: max of ‖(0,0,1)‖², ‖(0,1,1)‖², ‖(1,0,1)‖², ‖(1,1,1)‖² = 3
#eval
  let R_sq : ℚ := 3  -- max augmented norm squared
  let γ : ℚ := 1/4   -- example margin (need to compute actual margin)
  (convergenceBound γ R_sq, "theoretical max updates")
