import HarmonicBalls.Proofs.Sec11.ExhaustionDecoder

/-! # Singular internal-metric decoders on open exhaustions

Each observed pair may use its own cutoff radii. The normalized metric is
centered using a single continuous reference background. Section 8 uses
Leonardo Bonanno's LatticeProb formalization.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- A single measurable decoder represents countably many singular internal
metrics on increasing unions of sets separated from the origin. Its shifted
values represent Weyl-scaled singular metrics whenever those are length
metrics. -/
theorem IsWholePlaneGFF.exists_exhausted_singularMetric_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (f₀ : ℂ → ℝ) (hf₀ : Continuous f₀)
    (r : ℕ → ℕ → ℝ) (hr : ∀ n m, 0 < r n m)
    (U : ℕ → ℕ → Set ℂ) (hU : ∀ n m, IsOpen (U n m))
    (hmono : ∀ n, Monotone (U n))
    (haway : ∀ n m z, z ∈ U n m → r n m ≤ ‖z‖)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n m, (p n).1 ∈ U n m) (hξ : 0 ≤ ξ) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℕ → ℝ≥0∞, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ n, F (localModConstPairings 0 hC univ ω) n =
        ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f₀ z * ψ z)))) *
          internalMetric (D ω) (⋃ m, U n m) (p n).1 (p n).2) ∧
      ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → (∀ z, g z ≤ 0) →
        (∀ᵐ ω ∂P, IsEuclideanLengthMetric
          (fun x y => (weylScaling (D ω) ξ g x y).toReal)) →
        ∀ᵐ ω ∂P, ∀ n, F (localModConstPairings 0
          (fun ω => addFunPairing (hC ω) g) univ ω) n =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f₀ z) * ψ z)))) *
            internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
              (⋃ m, U n m) (p n).1 (p n).2 := by
  let f : ℕ → ℕ → ℂ → ℝ := fun n m z => -α * Real.log (max ‖z‖ (r n m))
  have hf (n m : ℕ) : Continuous (f n m) := by
    apply continuous_const.mul
    apply (continuous_norm.max continuous_const).log
    intro z
    exact ne_of_gt (lt_of_lt_of_le (hr n m) (le_max_right _ _))
  have hex (n m : ℕ) := h.exists_internal_singularMetric_cutoff_shift_decoder
    𝔇 h𝔇 hD hmetric ψ hψ hψint (hr n m) (fun _ => U n m)
    (fun _ => hU n m) (fun _ z hz => haway n m z hz) (fun _ => p n) (fun _ => hp n m)
  choose A hA hAbase hAshift using hex
  let a : ℕ → ℕ → ℝ≥0∞ := fun n m => ENNReal.ofReal
    (Real.exp (ξ * ((∫ z, f n m z * ψ z) - ∫ z, f₀ z * ψ z)))
  let F : (LocalZeroMeanTest univ → ℝ) → ℕ → ℝ≥0∞ :=
    fun v n => ⨅ m, a n m * A n m v 0
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro n
    apply Measurable.iInf
    intro m
    exact measurable_const.mul ((measurable_pi_apply 0).comp (hA n m))
  refine ⟨F, hF, ?_, ?_⟩
  · have hall : ∀ᵐ ω ∂P, ∀ n m,
        A n m (localModConstPairings 0 hC univ ω) 0 =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f n m z * ψ z)))) *
            internalMetric (D ω) (U n m) (p n).1 (p n).2 := by
      apply (ae_all_iff).2
      intro n
      apply (ae_all_iff).2
      intro m
      filter_upwards [hAbase n m] with ω hω
      exact hω 0
    filter_upwards [hall] with ω hω n
    change (⨅ m, a n m * A n m (localModConstPairings 0 hC univ ω) 0) = _
    have hn (m : ℕ) : a n m * ENNReal.ofReal
        (Real.exp (ξ * (-(hC ω ψ + ∫ z, f n m z * ψ z)))) =
        ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f₀ z * ψ z)))) := by
      simpa only [a, zero_add] using cutoff_normalization_factor_pairing ξ (hC ω ψ)
        ψ (fun _ => 0) f₀ (f n m) hψ continuous_const hf₀ (hf n m)
    calc
      (⨅ m, a n m * A n m (localModConstPairings 0 hC univ ω) 0) =
          ⨅ m, ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f₀ z * ψ z)))) *
            internalMetric (D ω) (U n m) (p n).1 (p n).2 := by
        apply iInf_congr
        intro m
        rw [hω n m, ← mul_assoc, hn m]
      _ = ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f₀ z * ψ z)))) *
          internalMetric (D ω) (⋃ m, U n m) (p n).1 (p n).2 := by
        rw [internalMetric_iUnion_of_monotone_isOpen _ (U n) (hU n) (hmono n),
          ENNReal.mul_iInf (fun ht _ => (ENNReal.ofReal_ne_top ht).elim)]
  · intro g hg hgc hgu hgmetric
    have hall : ∀ᵐ ω ∂P, ∀ n m,
        A n m (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) 0 =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f n m z) * ψ z)))) *
            internalMetric (fun x y => (weylScaling (𝔇 (hC ω)) ξ
              (fun z => g z + f n m z) x y).toReal) (U n m) (p n).1 (p n).2 := by
      apply (ae_all_iff).2
      intro n
      apply (ae_all_iff).2
      intro m
      filter_upwards [hAshift n m g hg] with ω hω
      exact hω 0
    have hrepr : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (D ω x y) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y := by
      filter_upwards [hD] with ω hω x y
      exact (hω x y).2
    have hcomp : ∀ᵐ ω ∂P, ∀ n x y,
        internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
          (⋃ m, U n m) x y =
        ⨅ m, internalMetric (fun x y => (weylScaling (𝔇 (hC ω)) ξ
          (fun z => g z + f n m z) x y).toReal) (U n m) x y := by
      apply (ae_all_iff).2
      intro n
      have ht := h.ae_internal_singularMetric_weylShift_eq_iInf_cutoff 𝔇 h𝔇 hrepr hmetric
        g hg hgc hgu hξ hgmetric (r n) (hr n) (fun _ => U n)
        (fun _ => hU n) (fun _ => hmono n) (fun _ m z hz => haway n m z hz)
      filter_upwards [ht] with ω hω x y
      exact hω 0 x y
    filter_upwards [hall, hcomp] with ω hω hωcomp n
    change (⨅ m, a n m * A n m
      (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) 0) = _
    calc
      (⨅ m, a n m * A n m
          (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) 0) =
          ⨅ m, ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f₀ z) * ψ z)))) *
            internalMetric (fun x y => (weylScaling (𝔇 (hC ω)) ξ
              (fun z => g z + f n m z) x y).toReal) (U n m) (p n).1 (p n).2 := by
        apply iInf_congr
        intro m
        rw [hω n m, ← mul_assoc]
        rw [show a n m * ENNReal.ofReal
          (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f n m z) * ψ z)))) = _ from
            cutoff_normalization_factor_pairing ξ (hC ω ψ) ψ g f₀ (f n m) hψ hg hf₀ (hf n m)]
      _ = ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f₀ z) * ψ z)))) *
          internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
            (⋃ m, U n m) (p n).1 (p n).2 := by
        rw [hωcomp n, ENNReal.mul_iInf (fun ht _ => (ENNReal.ofReal_ne_top ht).elim)]

/-- A joint metric decoder on punctured open sets, with a common continuous
reference background and arbitrary nonzero first endpoints. -/
theorem IsWholePlaneGFF.exists_punctured_singularMetric_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (f₀ : ℂ → ℝ) (hf₀ : Continuous f₀) (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n))
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ U n ∧ (p n).1 ≠ 0) (hξ : 0 ≤ ξ) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℕ → ℝ≥0∞, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ n, F (localModConstPairings 0 hC univ ω) n =
        ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f₀ z * ψ z)))) *
          internalMetric (D ω) (U n \ {0}) (p n).1 (p n).2) ∧
      ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → (∀ z, g z ≤ 0) →
        (∀ᵐ ω ∂P, IsEuclideanLengthMetric
          (fun x y => (weylScaling (D ω) ξ g x y).toReal)) →
        ∀ᵐ ω ∂P, ∀ n, F (localModConstPairings 0
          (fun ω => addFunPairing (hC ω) g) univ ω) n =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f₀ z) * ψ z)))) *
            internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
              (U n \ {0}) (p n).1 (p n).2 := by
  let r : ℕ → ℕ → ℝ := fun n m => min (‖(p n).1‖ / 2) (1 / (m + 1 : ℝ))
  let V : ℕ → ℕ → Set ℂ := fun n m => U n ∩ {z | r n m < ‖z‖}
  have hr (n m : ℕ) : 0 < r n m := by
    exact lt_min (div_pos (norm_pos_iff.mpr (hp n).2) (by norm_num)) (by positivity)
  have hopen (n m : ℕ) : IsOpen (V n m) :=
    (hU n).inter (isOpen_lt continuous_const continuous_norm)
  have hmono (n : ℕ) : Monotone (V n) := by
    intro m k hmk z hz
    refine ⟨hz.1, ?_⟩
    change r n k < ‖z‖
    apply lt_of_le_of_lt ?_ hz.2
    apply min_le_min_left
    gcongr
  have haway (n m : ℕ) (z : ℂ) (hz : z ∈ V n m) : r n m ≤ ‖z‖ := hz.2.le
  have hpV (n m : ℕ) : (p n).1 ∈ V n m := by
    refine ⟨(hp n).1, ?_⟩
    change r n m < ‖(p n).1‖
    have hpos := norm_pos_iff.mpr (hp n).2
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hunion (n : ℕ) : (⋃ m, V n m) = U n \ {0} := by
    apply subset_antisymm
    · intro z hz
      obtain ⟨m, hzm⟩ := mem_iUnion.mp hz
      refine ⟨hzm.1, ?_⟩
      simp only [mem_singleton_iff]
      intro hz0
      have hpos := (hr n m).trans hzm.2
      have hfalse : (0 : ℝ) < 0 := by simpa only [hz0, norm_zero] using hpos
      exact (lt_irrefl 0) hfalse
    · intro z hz
      have hz' : z ∈ ⋃ m : ℕ, U n ∩ {z : ℂ | 1 / (m + 1 : ℝ) < ‖z‖} := by
        rw [punctured_open_exhaustion]
        exact hz
      obtain ⟨m, hzm⟩ := mem_iUnion.mp hz'
      refine mem_iUnion.mpr ⟨m, hzm.1, ?_⟩
      change r n m < ‖z‖
      exact lt_of_le_of_lt (min_le_right _ _) hzm.2
  obtain ⟨F, hF, hb, hs⟩ := h.exists_exhausted_singularMetric_shift_decoder
    𝔇 h𝔇 hD hmetric ψ hψ hψint f₀ hf₀ r hr V hopen hmono haway p hpV hξ
  refine ⟨F, hF, ?_, ?_⟩
  · filter_upwards [hb] with ω hω n
    simpa only [hunion] using hω n
  · intro g hg hc hu hm
    filter_upwards [hs g hg hc hu hm] with ω hω n
    simpa only [hunion] using hω n

#print axioms IsWholePlaneGFF.exists_punctured_singularMetric_shift_decoder

#print axioms IsWholePlaneGFF.exists_exhausted_singularMetric_shift_decoder

end HarmonicBalls
