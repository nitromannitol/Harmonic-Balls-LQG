import HarmonicBalls.Proofs.GFF.MetricXiSign
import HarmonicBalls.Steps.Sec11.WeylScalingOrder

/-! # Normalized across-annulus laws of the zero-charge LQG metric

Credit: the whole-plane GFF `h^ℂ` used here, and its normalized affine invariance
(`WholePlaneGFFAffineInvariance`, proved as `wholePlaneGFFAffineInvariance_proved`), are due to Leonardo Bonanno.
As in `HarmonicBalls/Proofs/GFF/MetricXiSign.lean`, these lemmas hold for any realization of that field.

Setting. `h^ℂ` is a whole-plane GFF `IsWholePlaneGFF P hC hcirc` with zero charge (no logarithmic insertion), so the
metric is `𝔇 (hC ω)` for a `γ`-LQG metric `𝔇` with Weyl exponent `ξ` (`IsLQGMetric γ ξ 𝔇`), and `Q = lqgQ γ`.
The across-annulus distance is Pfeffer's `inf {D x y : |x - z₀| = a, |y - z₀| = b}` (arXiv:2104.04020, Axiom V of
Definition 1.6). With `c_r = r^{ξQ}`, the normalization of Axiom V is `r^{-ξQ} e^{-ξ h_r(0)}`, where
`h_r(0) = hcirc ω r 0`.

Results. For `r > 0`, the normalized functional `X_r = r^{-ξQ} e^{-ξ h_r(0)} · A_{𝔇(h^ℂ)}(r z₀; r a, r b)` equals,
almost surely, the across-annulus distance of the affinely normalized field `h^ℂ(r ·) - h^ℂ_r(0)`, which is again a
whole-plane GFF. Hence the law of `X_r` does not depend on `r > 0` (`normalizedAcross_identDistrib`), and the family
`(X_r)_{r > 0}` is tight and reciprocally tight (`normalizedAcross_tight`). Strict positivity and finiteness come from
the Euclidean topology of the metric and the compactness of the two circles (`annularAcross_pos_lt_top`).

Not in this file: the around-annulus length (`pfefferAround`, an infimum over separating loops) and any internal
diameter; see `docs/campaign/audits/MetricAnnulusScaleLaw.md`.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-! ### Definitions -/

/-- The across-annulus distance `A_D(z₀; a, b) = inf {D x y : |x - z₀| = a, |y - z₀| = b}` of Pfeffer
(arXiv:2104.04020, Axiom V of Definition 1.6). It has the formula of `pfefferAcross` in the staged file
`HarmonicBalls/Proposed/PfefferMetricScaling.lean`, restated here so that this module does not consume that file. -/
noncomputable def annularAcross (D : ℂ → ℂ → ℝ) (z₀ : ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ x ∈ Metric.sphere z₀ a, ⨅ y ∈ Metric.sphere z₀ b, ENNReal.ofReal (D x y)

/-- The zero-charge normalizing factor `r^{-ξQ} e^{-ξ h_r(0)}` of Axiom V with `c_r = r^{ξQ}` and `Q = lqgQ γ`,
where `h_r(0) = hcirc ω r 0` is the circle average of `h^ℂ`. The charge is zero, so there is no `f`-average. -/
noncomputable def zeroChargeNormalization (γ ξ : ℝ) {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) (r : ℝ) (ω : Ω) :
    ℝ≥0∞ :=
  ENNReal.ofReal (r ^ (-(ξ * lqgQ γ)) * Real.exp (-(ξ * hcirc ω r 0)))

/-- The normalized across-annulus functional `X_r = r^{-ξQ} e^{-ξ h_r(0)} · A_{𝔇(h^ℂ)}(r z₀; r a, r b)`. -/
noncomputable def normalizedAcross (γ ξ : ℝ) {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (z₀ : ℂ) (a b r : ℝ) (ω : Ω) : ℝ≥0∞ :=
  zeroChargeNormalization γ ξ hcirc r ω * annularAcross (𝔇 (hC ω)) ((r : ℂ) * z₀) (r * a) (r * b)

/-- The countable-dense reduction `T ↦ inf_{(x, y) ∈ A × B} 𝔇 T x y` of the across-annulus distance. -/
noncomputable def countableAcross (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (A B : Set ℂ) (T : (ℂ → ℝ) → ℝ) :
    ℝ≥0∞ :=
  ⨅ p : ↥(A ×ˢ B), ENNReal.ofReal (𝔇 T p.1.1 p.1.2)

/-- The band event `{ω | (n + 1)⁻¹ ≤ Y ω ≤ n + 1}`, increasing in `n`. -/
def annularBandEvent {Ω : Type*} (Y : Ω → ℝ≥0∞) (n : ℕ) : Set Ω :=
  {ω | ENNReal.ofReal ((n : ℝ) + 1)⁻¹ ≤ Y ω ∧ Y ω ≤ ENNReal.ofReal ((n : ℝ) + 1)}

/-! ### Facts about a Euclidean length metric -/

/-- A Euclidean length metric is jointly continuous: its `D`-balls are Euclidean neighbourhoods. -/
theorem isEuclideanLengthMetric_continuous {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) :
    Continuous fun p : ℂ × ℂ => D p.1 p.2 := by
  have hball : ∀ z : ℂ, ∀ ε : ℝ, 0 < ε → ∀ᶠ w in 𝓝 z, D z w < ε := by
    intro z ε hε
    have hopen : IsOpen {w | D z w < ε} := by
      refine (hD.isOpen_iff _).2 fun w hw => ⟨ε - D z w, ?_, fun v hv => ?_⟩
      · simp only [Set.mem_ofPred_eq] at hw
        linarith
      · simp only [Set.mem_ofPred_eq] at hw ⊢
        linarith [hD.triangle z w v]
    refine hopen.mem_nhds ?_
    show D z z < ε
    rw [hD.self_eq_zero]
    exact hε
  rw [continuous_iff_continuousAt]
  rintro ⟨z, w⟩
  unfold ContinuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  have e1 : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, w), D z p.1 < ε / 2 :=
    (continuous_fst.tendsto (z, w)).eventually (hball z (ε / 2) (by linarith))
  have e2 : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, w), D w p.2 < ε / 2 :=
    (continuous_snd.tendsto (z, w)).eventually (hball w (ε / 2) (by linarith))
  filter_upwards [e1, e2] with p hp1 hp2
  simp only [Real.dist_eq]
  rw [abs_lt]
  constructor
  · linarith [hD.triangle z w p.2, hD.triangle z p.1 w, hD.triangle p.1 p.2 w, hD.symm p.2 w, hD.symm p.1 z]
  · linarith [hD.triangle p.1 z p.2, hD.triangle z w p.2, hD.symm p.1 z, hD.symm p.2 w]

/-- Distinct points have positive `D`-distance. -/
theorem isEuclideanLengthMetric_pos_of_ne {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {x y : ℂ}
    (hxy : x ≠ y) : 0 < D x y := by
  have h0 : 0 ≤ D x y := by
    have h := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at h
    linarith
  exact lt_of_le_of_ne h0 fun h => hxy (hD.eq_of_eq_zero x y h.symm)

/-- A countable dense subset of a circle, in the Euclidean topology. -/
theorem exists_countable_dense_sphere (z : ℂ) (a : ℝ) :
    ∃ A : Set ℂ, A.Countable ∧ A ⊆ Metric.sphere z a ∧ Metric.sphere z a ⊆ closure A :=
  TopologicalSpace.exists_countable_dense_subset (Metric.sphere z a)

/-- For a jointly continuous, positive off-diagonal `D` and `0 < a < b`, the across-annulus distance is strictly
positive and finite: the infimum over the compact product of two disjoint circles is attained. -/
theorem annularAcross_pos_lt_top {D : ℂ → ℂ → ℝ} (hDc : Continuous fun p : ℂ × ℂ => D p.1 p.2)
    (hpos : ∀ x y : ℂ, x ≠ y → 0 < D x y) {z₀ : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < annularAcross D z₀ a b ∧ annularAcross D z₀ a b < ⊤ := by
  have hK : IsCompact (Metric.sphere z₀ a ×ˢ Metric.sphere z₀ b) :=
    (isCompact_sphere z₀ a).prod (isCompact_sphere z₀ b)
  have hne : (Metric.sphere z₀ a ×ˢ Metric.sphere z₀ b).Nonempty :=
    (NormedSpace.sphere_nonempty.2 ha.le).prod (NormedSpace.sphere_nonempty.2 (ha.trans hab).le)
  obtain ⟨⟨x₀, y₀⟩, hmem, hmin⟩ := hK.exists_isMinOn hne hDc.continuousOn
  have hx₀ : x₀ ∈ Metric.sphere z₀ a := (Set.mem_prod.1 hmem).1
  have hy₀ : y₀ ∈ Metric.sphere z₀ b := (Set.mem_prod.1 hmem).2
  have hne' : x₀ ≠ y₀ := by
    intro h
    have h1 := Metric.mem_sphere.1 hx₀
    have h2 := Metric.mem_sphere.1 hy₀
    rw [h] at h1
    linarith
  have hval : annularAcross D z₀ a b = ENNReal.ofReal (D x₀ y₀) := by
    refine le_antisymm ((iInf₂_le x₀ hx₀).trans (iInf₂_le y₀ hy₀)) ?_
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal ?_
    exact isMinOn_iff.1 hmin (x, y) ⟨hx, hy⟩
  rw [hval]
  exact ⟨ENNReal.ofReal_pos.2 (hpos x₀ y₀ hne'), ENNReal.ofReal_lt_top⟩

/-! ### Scaling -/

/-- Dilation by `r > 0` maps the circle `∂B_a(z₀)` onto the circle `∂B_{ra}(r z₀)`. -/
theorem sphere_smul_eq_image {r : ℝ} (hr : 0 < r) (z₀ : ℂ) (a : ℝ) :
    Metric.sphere ((r : ℂ) * z₀) (r * a) = (fun x : ℂ => (r : ℂ) * x) '' Metric.sphere z₀ a := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hdist : ∀ x : ℂ, dist ((r : ℂ) * x) ((r : ℂ) * z₀) = r * dist x z₀ := by
    intro x
    rw [Complex.dist_eq, Complex.dist_eq, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  ext x
  constructor
  · intro hx
    have hx' : dist x ((r : ℂ) * z₀) = r * a := Metric.mem_sphere.1 hx
    refine ⟨(r : ℂ)⁻¹ * x, Metric.mem_sphere.2 ?_, mul_inv_cancel_left₀ hr0 x⟩
    have h1 := hdist ((r : ℂ)⁻¹ * x)
    rw [mul_inv_cancel_left₀ hr0, hx'] at h1
    exact (mul_left_cancel₀ hr.ne' h1).symm
  · rintro ⟨x', hx', rfl⟩
    refine Metric.mem_sphere.2 ?_
    show dist ((r : ℂ) * x') ((r : ℂ) * z₀) = r * a
    rw [hdist, Metric.mem_sphere.1 hx']

/-- Scaling identity for the across-annulus distance: if `D(r x, r y) = c · E(x, y)` with `0 < c < ∞`, then
`A_D(r z₀; r a, r b) = c · A_E(z₀; a, b)`. -/
theorem annularAcross_smul {D : ℂ → ℂ → ℝ} {r : ℝ} (hr : 0 < r) (z₀ : ℂ) (a b : ℝ) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcT : c ≠ ⊤) {E : ℂ → ℂ → ℝ}
    (hDE : ∀ x y : ℂ, ENNReal.ofReal (D ((r : ℂ) * x) ((r : ℂ) * y)) = c * ENNReal.ofReal (E x y)) :
    annularAcross D ((r : ℂ) * z₀) (r * a) (r * b) = c * annularAcross E z₀ a b := by
  unfold annularAcross
  rw [sphere_smul_eq_image hr z₀ a, sphere_smul_eq_image hr z₀ b]
  simp only [iInf_image, hDE, ENNReal.mul_iInf_of_ne hc0 hcT]

/-- The zero-charge normalization: `e^{ξ(h_r(0) + Q log r)} = e^{ξ h_r(0)} r^{ξQ}`. -/
theorem exp_shift_eq {γ ξ r : ℝ} (hr : 0 < r) (hc : ℝ) :
    Real.exp (ξ * (hc + lqgQ γ * Real.log r)) = Real.exp (ξ * hc) * r ^ (ξ * lqgQ γ) := by
  rw [Real.rpow_def_of_pos hr, mul_add, Real.exp_add,
    show ξ * (lqgQ γ * Real.log r) = Real.log r * (ξ * lqgQ γ) by ring]

/-- The normalizing factor times the Weyl factor `e^{ξ(h_r(0) + Q log r)}` is `1`. -/
theorem zeroChargeNormalization_mul {γ ξ r : ℝ} (hr : 0 < r) (hc : ℝ) :
    ENNReal.ofReal (r ^ (-(ξ * lqgQ γ)) * Real.exp (-(ξ * hc))) *
      ENNReal.ofReal (Real.exp (ξ * (hc + lqgQ γ * Real.log r))) = 1 := by
  have hs : 0 < r ^ (ξ * lqgQ γ) := Real.rpow_pos_of_pos hr _
  have he : Real.exp (ξ * hc) ≠ 0 := (Real.exp_pos _).ne'
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le), exp_shift_eq hr hc,
    ← ENNReal.ofReal_one]
  congr 1
  rw [Real.rpow_neg hr.le, Real.exp_neg]
  field_simp

/-! ### The affine normalization and the zero-charge field -/

/-- Adding the constant `0` does not change a pairing functional. -/
theorem addFunPairing_const_zero (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => 0) = T := by
  funext φ
  simp [addFunPairing]

/-- The pullback `h^ℂ(r · )` shifted by `Q log r` is the affine normalized field `h^ℂ(r · ) - h^ℂ_r(0)` shifted by
`h^ℂ_r(0) + Q log r` (`affinePairing hC hcirc r 0` is `h^ℂ(r · ) - h^ℂ_r(0)`). -/
theorem affinePullback_eq_affinePairing {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    {r : ℝ} (hr : 0 < r) (γ : ℝ) (ω : Ω) :
    addFunPairing (affinePullbackPairing (hC ω) r 0) (fun _ => lqgQ γ * Real.log r) =
      addFunPairing (affinePairing hC hcirc (r : ℂ) 0 ω) (fun _ => hcirc ω r 0 + lqgQ γ * Real.log r) := by
  funext φ
  simp only [addFunPairing, affinePullbackPairing, affinePairing, Complex.norm_real,
    Real.norm_of_nonneg hr.le, sub_zero, integral_const_mul]
  ring

/-- The zero-charge field satisfies Axioms I–IV of `IsLQGMetric` (with `f = 0`). -/
theorem zeroCharge_satisfies {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) :
    SatisfiesLQGMetricAxioms P γ ξ 𝔇 hC := by
  have key := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h
    (fun _ => continuous_const) (fun _ => measurable_const)
  simpa only [addFunPairing_const_zero] using key

/-- Almost surely, the metric of the zero-charge field at the dilated points is the metric of the affinely normalized
field, up to the factor `e^{ξ(h_r(0) + Q log r)}` (coordinate change and Weyl scaling of `IsLQGMetric`). -/
theorem zeroCharge_scale_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ,
      ENNReal.ofReal (𝔇 (hC ω) ((r : ℂ) * x) ((r : ℂ) * y)) =
        ENNReal.ofReal (Real.exp (ξ * (hcirc ω r 0 + lqgQ γ * Real.log r))) *
          ENNReal.ofReal (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω) x y) := by
  have hg : IsWholePlaneGFF P (affinePairing hC hcirc (r : ℂ) 0) (affineCircle hcirc (r : ℂ) 0) :=
    wholePlaneGFFAffineInvariance_proved P hC hcirc h (r : ℂ) (by exact_mod_cast hr.ne') 0
  have hCax := zeroCharge_satisfies h𝔇 h
  have hgax := zeroCharge_satisfies h𝔇 hg
  filter_upwards [hCax.coordChange r hr 0, hgax.ae_weylScaling] with ω hcoord hweyl
  intro x y
  have h1 := hcoord x y
  simp only [add_zero] at h1
  rw [h1, affinePullback_eq_affinePairing hC hcirc hr γ ω]
  have h2 := hweyl (fun _ => hcirc ω r 0 + lqgQ γ * Real.log r) continuous_const x y
  have h3 := hweyl (fun _ => 0) continuous_const x y
  rw [addFunPairing_const_zero] at h3
  have h4 := weylScaling_add_const (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) ξ
    (hcirc ω r 0 + lqgQ γ * Real.log r) (fun _ => 0) x y
  simp only [zero_add] at h4
  rw [h2, h4, ← h3]

/-- Almost surely, the normalized across-annulus functional equals the across-annulus distance of the affinely
normalized field `h^ℂ(r · ) - h^ℂ_r(0)`. -/
theorem normalizedAcross_ae_eq_affine {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z₀ : ℂ) (a b : ℝ) :
    ∀ᵐ ω ∂P, normalizedAcross γ ξ hC hcirc 𝔇 z₀ a b r ω =
      annularAcross (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) z₀ a b := by
  filter_upwards [zeroCharge_scale_ae h𝔇 h hr] with ω hω
  have hc0 : ENNReal.ofReal (Real.exp (ξ * (hcirc ω r 0 + lqgQ γ * Real.log r))) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hcT : ENNReal.ofReal (Real.exp (ξ * (hcirc ω r 0 + lqgQ γ * Real.log r))) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  unfold normalizedAcross zeroChargeNormalization
  rw [annularAcross_smul hr z₀ a b hc0 hcT hω, ← mul_assoc, zeroChargeNormalization_mul hr (hcirc ω r 0), one_mul]

/-! ### Countable reduction and common marginal law -/

/-- The countable reduction is measurable for the σ-algebra of the pairings. -/
theorem countableAcross_measurable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {A B : Set ℂ} (hA : A.Countable) (hB : B.Countable) :
    Measurable[distributionMeasurableSpace] (countableAcross 𝔇 A B) := by
  have : Countable ↥(A ×ˢ B) := (hA.prod hB).to_subtype
  unfold countableAcross
  exact Measurable.iInf fun p => ENNReal.measurable_ofReal.comp (h𝔇.measurable_apply _ _)

/-- Along countable dense subsets of the two circles, the across-annulus distance of a jointly continuous metric is the
infimum over the countable product. -/
theorem annularAcross_eq_countableAcross {D : ℂ → ℂ → ℝ} (hDc : Continuous fun p : ℂ × ℂ => D p.1 p.2)
    {z₀ : ℂ} {a b : ℝ} {A B : Set ℂ} (hAS : A ⊆ Metric.sphere z₀ a) (hAd : Metric.sphere z₀ a ⊆ closure A)
    (hBS : B ⊆ Metric.sphere z₀ b) (hBd : Metric.sphere z₀ b ⊆ closure B) :
    annularAcross D z₀ a b = ⨅ p : ↥(A ×ˢ B), ENNReal.ofReal (D p.1.1 p.1.2) := by
  apply le_antisymm
  · refine le_iInf fun p => ?_
    exact (iInf₂_le p.1.1 (hAS (Set.mem_prod.1 p.2).1)).trans (iInf₂_le p.1.2 (hBS (Set.mem_prod.1 p.2).2))
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    have hU : IsOpen {q : ℂ × ℂ | ENNReal.ofReal (D q.1 q.2) < c} :=
      isOpen_lt (ENNReal.continuous_ofReal.comp hDc) continuous_const
    have hmem : ((x, y) : ℂ × ℂ) ∈ closure (A ×ˢ B) := by
      rw [closure_prod_eq]
      exact ⟨hAd hx, hBd hy⟩
    obtain ⟨q, hqU, hqAB⟩ := mem_closure_iff.1 hmem _ hU hc
    exact (iInf_le _ ⟨q, hqAB⟩).trans hqU.le

/-- Equality in law of a.s.-equal random variables: a congruence for `IdentDistrib`. -/
theorem identDistrib_congr_ae {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    {P : Measure Ω} {P' : Measure Ω'} {f f' : Ω → E} {g g' : Ω' → E}
    (h : IdentDistrib f g P P') (hf : f =ᵐ[P] f') (hg : g =ᵐ[P'] g') : IdentDistrib f' g' P P' :=
  ⟨h.aemeasurable_fst.congr hf, h.aemeasurable_snd.congr hg,
    by rw [← Measure.map_congr hf, ← Measure.map_congr hg]; exact h.map_eq⟩

/-- The across-annulus distance of the affinely normalized field has the law of that of the zero-charge field. -/
theorem annularAcross_identDistrib_affine {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z₀ : ℂ) (a b : ℝ) :
    IdentDistrib (fun ω => annularAcross (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) z₀ a b)
      (fun ω => annularAcross (𝔇 (hC ω)) z₀ a b) P P := by
  obtain ⟨A, hAc, hAS, hAd⟩ := exists_countable_dense_sphere z₀ a
  obtain ⟨B, hBc, hBS, hBd⟩ := exists_countable_dense_sphere z₀ b
  have hg : IsWholePlaneGFF P (affinePairing hC hcirc (r : ℂ) 0) (affineCircle hcirc (r : ℂ) 0) :=
    wholePlaneGFFAffineInvariance_proved P hC hcirc h (r : ℂ) (by exact_mod_cast hr.ne') 0
  have hCax := zeroCharge_satisfies h𝔇 h
  have hgax := zeroCharge_satisfies h𝔇 hg
  obtain ⟨F, hFm, hFeq⟩ := exists_common_observable_of_distribution_measurable
    (countableAcross 𝔇 A B) (countableAcross_measurable h𝔇 hAc hBc)
  have hdF : IdentDistrib (fun ω => countableAcross 𝔇 A B (affinePairing hC hcirc (r : ℂ) 0 ω))
      (fun ω => countableAcross 𝔇 A B (hC ω)) P P := by
    have := (hg.identDistrib_observables_across_spaces h).comp hFm
    simp only [Function.comp_def, hFeq] at this
    exact this
  refine identDistrib_congr_ae hdF ?_ ?_
  · filter_upwards [hgax.ae_isEuclideanLengthMetric] with ω hω
    exact (annularAcross_eq_countableAcross (isEuclideanLengthMetric_continuous hω) hAS hAd hBS hBd).symm
  · filter_upwards [hCax.ae_isEuclideanLengthMetric] with ω hω
    exact (annularAcross_eq_countableAcross (isEuclideanLengthMetric_continuous hω) hAS hAd hBS hBd).symm

/-- **Common marginal law.** For every `r > 0`, the normalized across-annulus functional `X_r` has the law of the
across-annulus distance of the zero-charge field; the law does not depend on `r`. -/
theorem normalizedAcross_identDistrib {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z₀ : ℂ) (a b : ℝ) :
    IdentDistrib (fun ω => normalizedAcross γ ξ hC hcirc 𝔇 z₀ a b r ω)
      (fun ω => annularAcross (𝔇 (hC ω)) z₀ a b) P P := by
  refine identDistrib_congr_ae (annularAcross_identDistrib_affine h𝔇 h hr z₀ a b) ?_
    (Filter.EventuallyEq.refl _ _)
  filter_upwards [normalizedAcross_ae_eq_affine h𝔇 h hr z₀ a b] with ω hω
  exact hω.symm

/-- Almost surely, the across-annulus distance of the zero-charge field lies in `(0, ∞)`. -/
theorem annularAcross_ae_pos_lt_top {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {z₀ : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᵐ ω ∂P, 0 < annularAcross (𝔇 (hC ω)) z₀ a b ∧ annularAcross (𝔇 (hC ω)) z₀ a b < ⊤ := by
  filter_upwards [(zeroCharge_satisfies h𝔇 h).ae_isEuclideanLengthMetric] with ω hω
  exact annularAcross_pos_lt_top (isEuclideanLengthMetric_continuous hω)
    (fun x y hxy => isEuclideanLengthMetric_pos_of_ne hω hxy) ha hab

/-! ### Tightness -/

/-- The band events increase with `n`. -/
theorem annularBandEvent_mono {Ω : Type*} (Y : Ω → ℝ≥0∞) : Monotone (annularBandEvent Y) := by
  intro m n hmn ω hω
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  simp only [annularBandEvent, Set.mem_ofPred_eq] at hω ⊢
  exact ⟨le_trans (ENNReal.ofReal_le_ofReal (inv_anti₀ hm hmn')) hω.1,
    le_trans hω.2 (ENNReal.ofReal_le_ofReal hmn')⟩

/-- If `Y` is a.s. in `(0, ∞)`, the band events have probability at least `1 - ε` for some `n`. -/
theorem annularBand_exists {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ≥0∞} (hY : ∀ᵐ ω ∂P, 0 < Y ω ∧ Y ω < ⊤) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N : ℕ, ENNReal.ofReal (1 - ε) ≤ P (annularBandEvent Y N) := by
  have hcover : ∀ᵐ ω ∂P, ω ∈ ⋃ n, annularBandEvent Y n := by
    filter_upwards [hY] with ω hω
    obtain ⟨h0, htop⟩ := hω
    obtain ⟨t, ht, hYt⟩ : ∃ t : ℝ, 0 < t ∧ Y ω = ENNReal.ofReal t :=
      ⟨(Y ω).toReal, ENNReal.toReal_pos h0.ne' htop.ne, (ENNReal.ofReal_toReal htop.ne).symm⟩
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / t + t)
    have hinv : 1 / t ≤ (N : ℝ) := by linarith [one_div_nonneg.2 ht.le]
    have h1t : 1 ≤ (N : ℝ) * t := (div_le_iff₀ ht).1 hinv
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    simp only [annularBandEvent, Set.mem_ofPred_eq]
    rw [hYt]
    refine ⟨ENNReal.ofReal_le_ofReal ?_, ENNReal.ofReal_le_ofReal ?_⟩
    · have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      nlinarith
    · linarith [one_div_nonneg.2 ht.le]
  have hunion : P (⋃ n, annularBandEvent Y n) = 1 := by
    rw [measure_congr ((ae_eq_univ (s := ⋃ n, annularBandEvent Y n)).2 (ae_iff.1 hcover)), measure_univ]
  have hlim : Tendsto (fun n => P (annularBandEvent Y n)) atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := P) (annularBandEvent_mono Y)
    rwa [hunion] at h
  have hlt : ENNReal.ofReal (1 - ε) < 1 := ENNReal.ofReal_lt_one.2 (by linarith)
  obtain ⟨N, hN⟩ := (hlim.eventually (lt_mem_nhds hlt)).exists
  exact ⟨N, hN.le⟩

/-- **Tightness and reciprocal tightness** of the normalized across-annulus laws, uniformly in `r > 0`: for each
`ε ∈ (0, 1)` there is `M > 0` with `P(M⁻¹ ≤ X_r ≤ M) ≥ 1 - ε` for all `r > 0`. -/
theorem normalizedAcross_tight {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {z₀ : ℂ} {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (1 - ε) ≤
        P {ω | ENNReal.ofReal M⁻¹ ≤ normalizedAcross γ ξ hC hcirc 𝔇 z₀ a b r ω ∧
          normalizedAcross γ ξ hC hcirc 𝔇 z₀ a b r ω ≤ ENNReal.ofReal M} := by
  intro ε hε0 hε1
  have : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨N, hN⟩ := annularBand_exists (Y := fun ω => annularAcross (𝔇 (hC ω)) z₀ a b)
    (annularAcross_ae_pos_lt_top h𝔇 h (z₀ := z₀) ha hab) hε0 hε1
  refine ⟨(N : ℝ) + 1, by positivity, fun r hr => ?_⟩
  have hs : MeasurableSet (Set.Icc (ENNReal.ofReal ((N : ℝ) + 1)⁻¹) (ENNReal.ofReal ((N : ℝ) + 1))) :=
    measurableSet_Icc
  have hmeas := (normalizedAcross_identDistrib h𝔇 h hr z₀ a b).measure_mem_eq hs
  calc ENNReal.ofReal (1 - ε)
      ≤ P (annularBandEvent (fun ω => annularAcross (𝔇 (hC ω)) z₀ a b) N) := hN
    _ = P ((fun ω => annularAcross (𝔇 (hC ω)) z₀ a b) ⁻¹'
          Set.Icc (ENNReal.ofReal ((N : ℝ) + 1)⁻¹) (ENNReal.ofReal ((N : ℝ) + 1))) := rfl
    _ = P ((fun ω => normalizedAcross γ ξ hC hcirc 𝔇 z₀ a b r ω) ⁻¹'
          Set.Icc (ENNReal.ofReal ((N : ℝ) + 1)⁻¹) (ENNReal.ofReal ((N : ℝ) + 1))) := hmeas.symm
    _ = P {ω | ENNReal.ofReal ((N : ℝ) + 1)⁻¹ ≤ normalizedAcross γ ξ hC hcirc 𝔇 z₀ a b r ω ∧
          normalizedAcross γ ξ hC hcirc 𝔇 z₀ a b r ω ≤ ENNReal.ofReal ((N : ℝ) + 1)} := rfl

#print axioms normalizedAcross_identDistrib
#print axioms normalizedAcross_tight
#print axioms annularAcross_ae_pos_lt_top

end HarmonicBalls
