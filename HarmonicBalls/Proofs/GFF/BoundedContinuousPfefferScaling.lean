import HarmonicBalls.Proofs.GFF.PureGFFPfefferCrossingTightness
import HarmonicBalls.Proofs.GFF.ContinuousShiftWeakMetricAxioms
import HarmonicBalls.FirstPass.S11m.LocalDecoder
import HarmonicBalls.Steps.Sec11.PinchLocalContraction

/-! # Axiom V of Pfeffer's Definition 1.6 for a whole-plane GFF plus a bounded continuous function

Sources: Pfeffer, *Weak Liouville quantum gravity metrics with matter central charge up to 25*, arXiv:2104.04020v3,
Definition 1.6 (p. 6), Axiom V and the bound (1.7); Proposition 2.4, which states Axiom V for a whole-plane GFF plus a
bounded continuous function; and the Weyl scaling relation `D_{h'} = e^{ξ (h' - h)} · D_h` for two such fields
(Section 2.1, after Proposition 2.1). The Weyl scaling is used in the form of the almost sure Weyl scaling for all
continuous functions at once of a `γ`-LQG metric (Gwynne–Miller, arXiv:1905.00383v3, Section 1.2, p. 6).

Setting. `𝔇` is a `γ`-LQG metric with Weyl exponent `ξ` (`IsLQGMetric γ ξ 𝔇`), `h^ℂ` is a whole-plane GFF
(`IsWholePlaneGFF P hC hcirc`) and `f` is a random continuous function, measurable in `ω` at every point, which is
almost surely globally bounded: for almost every `ω` there is `K` with `|f ω z| ≤ K` for all `z`. The bound `K` may
depend on `ω`.

Results.
* `IsLQGMetric.boundedContinuousShift_pfefferAxiomVScale`: Axiom V for `h^ℂ + f`, with the scaling constants
  `c_r = r^{ξQ}`, `Q = 2/γ + γ/2`, of the case `f = 0` (`IsLQGMetric.pureGFF_pfefferAxiomVScale`).
* `IsLQGMetric.boundedContinuousShift_pfefferWeakAxioms`: with Axioms I–IV
  (`IsLQGMetric.continuousShift_pfefferWeakAxioms_one_to_four`), all of `PfefferWeakAxioms` hold for `h^ℂ + f`.

Argument. If `|f| ≤ K` on `ℂ`, Weyl scaling gives `e^{-|ξ| K} D_{h^ℂ} ≤ D_{h^ℂ + f} ≤ e^{|ξ| K} D_{h^ℂ}`, and every
circle average of `f` lies in `[-K, K]`. Hence the normalized distances across and around a scaled annulus for
`h^ℂ + f` are within the factor `e^{2 |ξ| K}` of those for `h^ℂ`. The events `{sup |f| ≤ n}` are measurable (by
continuity, a countable dense set of points suffices) and increase to an almost sure event, so the tightness for
`h^ℂ` transfers (`PfefferTightAcrossScales.of_ae_comparison`).

Scope. Unbounded `f` is not treated here.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

private lemma addFunPairing_fun_zero (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => 0) = T := by
  funext φ
  simp [addFunPairing]

/-- For a Euclidean length metric `D` and a weight `g` with `|g| ≤ K`, the Weyl scaling `e^{ξ g} · D` lies between
`e^{-|ξ| K} D` and `e^{|ξ| K} D`. -/
theorem IsEuclideanLengthMetric.weylScaling_le_and_ge_of_abs_le {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (ξ : ℝ) {g : ℂ → ℝ} {K : ℝ} (hg : ∀ z, |g z| ≤ K) (u v : ℂ) :
    weylScaling D ξ g u v ≤ ENNReal.ofReal (Real.exp (|ξ| * K)) * ENNReal.ofReal (D u v) ∧
      ENNReal.ofReal (D u v) ≤ ENNReal.ofReal (Real.exp (|ξ| * K)) * weylScaling D ξ g u v := by
  have hb : ∀ z, |ξ * g z| ≤ |ξ| * K := fun z => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hg z) (abs_nonneg ξ)
  have hξ1 : weylScaling D ξ g u v = weylScaling D 1 (fun x => ξ * g x) u v := by
    simp only [weylScaling, one_mul]
  have hup : weylScaling D 1 (fun x => ξ * g x) u v ≤ weylScaling D 1 (fun _ => |ξ| * K) u v :=
    S11m.weylScaling_mono zero_le_one (fun z => (abs_le.1 (hb z)).2) u v
  have hlow : weylScaling D 1 (fun _ => -(|ξ| * K)) u v ≤ weylScaling D 1 (fun x => ξ * g x) u v :=
    S11m.weylScaling_mono zero_le_one (fun z => (abs_le.1 (hb z)).1) u v
  rw [S11m.weylScaling_const_eq_mul_ofReal hD, one_mul] at hup
  rw [S11m.weylScaling_const_eq_mul_ofReal hD, one_mul] at hlow
  rw [hξ1]
  refine ⟨hup, ?_⟩
  calc ENNReal.ofReal (D u v)
      = ENNReal.ofReal (Real.exp (|ξ| * K)) *
          (ENNReal.ofReal (Real.exp (-(|ξ| * K))) * ENNReal.ofReal (D u v)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ _ := by gcongr

/-- A pointwise comparison `D ≤ L · E` of distances passes to the distances across every annulus. -/
theorem pfefferAcross_le_ofReal_mul {D E : ℂ → ℂ → ℝ} {L : ℝ} (hL : 0 < L)
    (hDE : ∀ u v, ENNReal.ofReal (D u v) ≤ ENNReal.ofReal L * ENNReal.ofReal (E u v)) (z₀ : ℂ) (a b : ℝ) :
    pfefferAcross D z₀ a b ≤ ENNReal.ofReal L * pfefferAcross E z₀ a b := by
  have h0 : ENNReal.ofReal L ≠ 0 := (ENNReal.ofReal_pos.2 hL).ne'
  unfold pfefferAcross
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  exact iInf₂_mono fun x _ => iInf₂_mono fun y _ => hDE x y

/-- A pointwise comparison `D ≤ L · E` of distances passes to the distances around every annulus. -/
theorem pfefferAround_le_ofReal_mul {D E : ℂ → ℂ → ℝ} {L : ℝ} (hL : 0 < L)
    (hDE : ∀ u v, ENNReal.ofReal (D u v) ≤ ENNReal.ofReal L * ENNReal.ofReal (E u v)) (z₀ : ℂ) (a b : ℝ) :
    pfefferAround D z₀ a b ≤ ENNReal.ofReal L * pfefferAround E z₀ a b := by
  have h0 : ENNReal.ofReal L ≠ 0 := (ENNReal.ofReal_pos.2 hL).ne'
  unfold pfefferAround
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_mono fun z => iInf₂_mono fun P _ => ?_
  rw [← pathLength_const_mul E L hL.le P]
  exact pathLength_le_of_ofReal_le_on (U := univ)
    (fun x _ y _ => by rw [ENNReal.ofReal_mul hL.le]; exact hDE x y) P (fun _ => mem_univ _)

/-- The circle averages of a function bounded by `K` in absolute value are bounded by `K`. -/
theorem abs_pfefferCircleAverage_le {g : ℂ → ℝ} {K : ℝ} (hg : ∀ z, |g z| ≤ K) (r : ℝ) (z : ℂ) :
    |pfefferCircleAverage g r z| ≤ K := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 2 * Real.pi) (C := K)
    (f := fun θ : ℝ => g (z + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) fun θ _ => by
      rw [Real.norm_eq_abs]
      exact hg _
  simp only [Real.norm_eq_abs, sub_zero] at hI
  rw [abs_of_pos hpi] at hI
  unfold pfefferCircleAverage
  rw [abs_mul, abs_inv, abs_of_pos hpi, inv_mul_le_iff₀ hpi]
  linarith

private lemma ofReal_mul_exp_le {A u v s : ℝ} (h : u ≤ v + s) :
    ENNReal.ofReal (A * Real.exp u) ≤ ENNReal.ofReal (Real.exp s) * ENNReal.ofReal (A * Real.exp v) := by
  rcases le_or_gt A 0 with hA | hA
  · rw [ENNReal.ofReal_of_nonpos (by nlinarith [Real.exp_pos u])]
    exact zero_le
  · rw [← ENNReal.ofReal_mul (Real.exp_pos s).le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc A * Real.exp u ≤ A * Real.exp (v + s) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h) hA.le
      _ = Real.exp s * (A * Real.exp v) := by rw [Real.exp_add]; ring

private lemma pfefferNormalization_le_exp_mul {Ω : Type*} {ξ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {f g : Ω → ℂ → ℝ} {c : ℝ → ℝ} {r s : ℝ} {ω : Ω}
    (h : |ξ * pfefferCircleAverage (f ω) r 0 - ξ * pfefferCircleAverage (g ω) r 0| ≤ s) :
    pfefferNormalization ξ hcirc f c r ω ≤
      ENNReal.ofReal (Real.exp s) * pfefferNormalization ξ hcirc g c r ω := by
  unfold pfefferNormalization
  refine ofReal_mul_exp_le ?_
  have := (abs_le.1 h).1
  linarith [mul_add ξ (hcirc ω r 0) (pfefferCircleAverage (f ω) r 0),
    mul_add ξ (hcirc ω r 0) (pfefferCircleAverage (g ω) r 0)]

private lemma pfefferNormalization_bounds {Ω : Type*} {ξ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {f : Ω → ℂ → ℝ}
    {c : ℝ → ℝ} {ω : Ω} {K : ℝ} (hK : ∀ z, |f ω z| ≤ K) (r : ℝ) :
    pfefferNormalization ξ hcirc f c r ω ≤
        ENNReal.ofReal (Real.exp (|ξ| * K)) * pfefferNormalization ξ hcirc (fun _ _ => 0) c r ω ∧
      pfefferNormalization ξ hcirc (fun _ _ => 0) c r ω ≤
        ENNReal.ofReal (Real.exp (|ξ| * K)) * pfefferNormalization ξ hcirc f c r ω := by
  have h0 : pfefferCircleAverage (fun _ : ℂ => (0 : ℝ)) r 0 = 0 := by simp [pfefferCircleAverage]
  have hs : |ξ * pfefferCircleAverage (f ω) r 0 - ξ * pfefferCircleAverage (fun _ : ℂ => (0 : ℝ)) r 0| ≤
      |ξ| * K := by
    rw [h0, mul_zero, sub_zero, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_pfefferCircleAverage_le hK r 0) (abs_nonneg ξ)
  exact ⟨pfefferNormalization_le_exp_mul hs, pfefferNormalization_le_exp_mul (by rwa [abs_sub_comm])⟩

private lemma mul_le_exp_two_mul {N₁ N₂ A₁ A₂ : ℝ≥0∞} {s : ℝ} (hN : N₁ ≤ ENNReal.ofReal (Real.exp s) * N₂)
    (hA : A₁ ≤ ENNReal.ofReal (Real.exp s) * A₂) :
    N₁ * A₁ ≤ ENNReal.ofReal (Real.exp (2 * s)) * (N₂ * A₂) := by
  calc N₁ * A₁ ≤ (ENNReal.ofReal (Real.exp s) * N₂) * (ENNReal.ofReal (Real.exp s) * A₂) := mul_le_mul' hN hA
    _ = _ := by rw [two_mul, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]; ring

/-- Tightness across scales (`PfefferTightAcrossScales`) passes from `X` to `Y` when, almost surely, on each event
`E n` the two families are within the factor `L n` of each other at every scale, and the complements of the events
`E n` have arbitrarily small probability. -/
theorem PfefferTightAcrossScales.of_ae_comparison {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : ℝ → Ω → ℝ≥0∞} (hX : PfefferTightAcrossScales P X) {E : ℕ → Set Ω} {L : ℕ → ℝ}
    (hL : ∀ n, 0 < L n) (hE : ∀ ε : ℝ, 0 < ε → ∃ n, P (E n)ᶜ ≤ ENNReal.ofReal ε)
    (hXY : ∀ᵐ ω ∂P, ∀ n, ω ∈ E n → ∀ r : ℝ, 0 < r →
      Y r ω ≤ ENNReal.ofReal (L n) * X r ω ∧ X r ω ≤ ENNReal.ofReal (L n) * Y r ω) :
    PfefferTightAcrossScales P Y := by
  intro ε hε hε1
  obtain ⟨M₀, hM₀, hM₀r⟩ := hX (ε / 2) (by linarith) (by linarith)
  obtain ⟨n, hn⟩ := hE (ε / 2) (by linarith)
  have hLn := hL n
  have key : ∀ G T S : Set Ω, (∀ ω ∈ G, ω ∈ E n → ω ∈ S → ω ∈ T) → P Sᶜ = 0 →
      ENNReal.ofReal (1 - ε / 2) ≤ P G → ENNReal.ofReal (1 - ε) ≤ P T := by
    intro G T S hGT hS hG
    have hsub : G ⊆ T ∪ ((E n)ᶜ ∪ Sᶜ) := by
      intro ω hω
      by_cases h1 : ω ∈ E n
      · by_cases h2 : ω ∈ S
        · exact Or.inl (hGT ω hω h1 h2)
        · exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl h1)
    have h1 : ENNReal.ofReal (1 - ε / 2) ≤ P T + ENNReal.ofReal (ε / 2) :=
      calc ENNReal.ofReal (1 - ε / 2) ≤ P G := hG
        _ ≤ P (T ∪ ((E n)ᶜ ∪ Sᶜ)) := measure_mono hsub
        _ ≤ P T + (P (E n)ᶜ + P Sᶜ) :=
          (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
        _ ≤ P T + ENNReal.ofReal (ε / 2) := by rw [hS, add_zero]; gcongr
    have hsplit : ENNReal.ofReal (1 - ε / 2) = ENNReal.ofReal (1 - ε) + ENNReal.ofReal (ε / 2) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring
    rw [hsplit] at h1
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h1
  refine ⟨M₀ * L n, mul_pos hM₀ hLn, fun r hr => ?_⟩
  obtain ⟨S, hS, hSp⟩ := hXY.exists_mem
  refine key _ _ S (fun ω hω hωE hωS => ?_) (mem_ae_iff.1 hS) (hM₀r r hr)
  obtain ⟨hYX, hXY'⟩ := hSp ω hωS n hωE r hr
  refine ⟨?_, ?_⟩
  · calc ENNReal.ofReal (M₀ * L n)⁻¹ = ENNReal.ofReal (L n)⁻¹ * ENNReal.ofReal M₀⁻¹ := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hLn.le), mul_inv_rev]
      _ ≤ ENNReal.ofReal (L n)⁻¹ * (ENNReal.ofReal (L n) * Y r ω) := by
          gcongr; exact hω.1.trans hXY'
      _ = Y r ω := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hLn.le), inv_mul_cancel₀ hLn.ne',
            ENNReal.ofReal_one, one_mul]
  · calc Y r ω ≤ ENNReal.ofReal (L n) * X r ω := hYX
      _ ≤ ENNReal.ofReal (L n) * ENNReal.ofReal M₀ := by gcongr; exact hω.2
      _ = ENNReal.ofReal (M₀ * L n) := by rw [← ENNReal.ofReal_mul hLn.le, mul_comm]

/-- For a random continuous function that is measurable at every point and almost surely globally bounded, the
events `{|f| ≤ n on ℂ}` have complements of arbitrarily small probability. -/
theorem exists_nat_measure_compl_abs_le_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {f : Ω → ℂ → ℝ} (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ x, Measurable fun ω => f ω x)
    (hbd : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ z, |f ω z| ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, P {ω | ∀ z, |f ω z| ≤ n}ᶜ ≤ ENNReal.ofReal ε := by
  obtain ⟨s, hs, hsd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hmeas : ∀ n : ℕ, MeasurableSet {ω | ∀ z, |f ω z| ≤ n} := by
    intro n
    have heq : {ω | ∀ z, |f ω z| ≤ n} = ⋂ z ∈ s, {ω | |f ω z| ≤ n} := by
      ext ω
      simp only [Set.mem_ofPred_eq, mem_iInter]
      refine ⟨fun h z _ => h z, fun h z => ?_⟩
      have hcl : IsClosed {z | |f ω z| ≤ n} := isClosed_le (continuous_abs.comp (hf ω)) continuous_const
      have hsub : closure s ⊆ {z | |f ω z| ≤ n} := hcl.closure_subset_iff.2 h
      exact hsub (by rw [hsd.closure_eq]; exact mem_univ z)
    rw [heq]
    exact MeasurableSet.biInter hs fun z _ =>
      measurableSet_le (continuous_abs.measurable.comp (hfm z)) measurable_const
  have hanti : Antitone fun n : ℕ => {ω | ∀ z, |f ω z| ≤ n}ᶜ := by
    intro m n hmn
    exact compl_subset_compl.2 fun ω h z => (h z).trans (Nat.cast_le.2 hmn)
  have hlim := tendsto_measure_iInter_atTop (fun n => (hmeas n).compl.nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  have hnull : P (⋂ n : ℕ, {ω | ∀ z, |f ω z| ≤ n}ᶜ) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hbd)
    simp only [mem_iInter, mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    simp only [Set.mem_ofPred_eq, not_exists, not_forall, not_le]
    intro K
    obtain ⟨n, hn⟩ := exists_nat_ge K
    obtain ⟨z, hz⟩ := hω n
    exact ⟨z, hn.trans_lt hz⟩
  rw [hnull] at hlim
  exact ((ENNReal.tendsto_nhds_zero.1 hlim) _ (ENNReal.ofReal_pos.2 hε)).exists

/-- **Axiom V of Pfeffer's Definition 1.6 for a whole-plane GFF plus a bounded continuous function.** For a `γ`-LQG
metric `𝔇` with Weyl exponent `ξ`, a whole-plane GFF `h^ℂ` and a random continuous function `f`, measurable at every
point and almost surely globally bounded, the scaling constants `c_r = r^{ξQ}`, `Q = 2/γ + γ/2`, satisfy Axiom V for
the field `h^ℂ + f`: positivity, tightness and reciprocal tightness across and around every scaled annulus, and the
bound (1.7). -/
theorem IsLQGMetric.boundedContinuousShift_pfefferAxiomVScale {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ x, Measurable fun ω => f ω x)
    (hbd : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ z, |f ω z| ≤ K) :
    PfefferAxiomVScale P ξ 𝔇 hC hcirc f (fun r => r ^ (ξ * lqgQ γ)) := by
  have hP : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨hc, hV0, hΛ⟩ := h𝔇.pureGFF_pfefferAxiomVScale h
  have hS0 := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h (fun _ => continuous_const)
    (fun _ => measurable_const)
  have hcmp : ∀ᵐ ω ∂P, ∀ n : ℕ, (∀ z, |f ω z| ≤ n) → ∀ u v : ℂ,
      ENNReal.ofReal (𝔇 (pfefferField hC f ω) u v) ≤ ENNReal.ofReal (Real.exp (|ξ| * n)) *
          ENNReal.ofReal (𝔇 (pfefferField hC (fun _ _ => 0) ω) u v) ∧
        ENNReal.ofReal (𝔇 (pfefferField hC (fun _ _ => 0) ω) u v) ≤ ENNReal.ofReal (Real.exp (|ξ| * n)) *
          ENNReal.ofReal (𝔇 (pfefferField hC f ω) u v) := by
    filter_upwards [hS0.ae_isEuclideanLengthMetric, hS0.ae_weylScaling] with ω hE hW n hn u v
    have h0 : pfefferField hC (fun _ _ => 0) ω = hC ω := addFunPairing_fun_zero (hC ω)
    simp only [addFunPairing_fun_zero] at hE hW
    rw [h0, show pfefferField hC f ω = addFunPairing (hC ω) (f ω) from rfl, hW (f ω) (hf ω) u v]
    exact hE.weylScaling_le_and_ge_of_abs_le ξ hn u v
  have hev : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, P {ω | ∀ z, |f ω z| ≤ n}ᶜ ≤ ENNReal.ofReal ε :=
    fun ε hε => exists_nat_measure_compl_abs_le_le hf hfm hbd hε
  refine ⟨hc, fun z₀ a b ha hab => ?_, hΛ⟩
  obtain ⟨hX1, hX2⟩ := hV0 z₀ a b ha hab
  constructor
  · refine hX1.of_ae_comparison (E := fun n : ℕ => {ω | ∀ z, |f ω z| ≤ n})
      (L := fun n : ℕ => Real.exp (2 * (|ξ| * n))) (fun n => Real.exp_pos _) hev ?_
    filter_upwards [hcmp] with ω hω n hn r _
    have hn' : ∀ z, |f ω z| ≤ (n : ℝ) := hn
    obtain ⟨hN1, hN2⟩ := pfefferNormalization_bounds (ξ := ξ) (hcirc := hcirc)
      (c := fun r => r ^ (ξ * lqgQ γ)) hn' r
    exact ⟨mul_le_exp_two_mul hN1
        (pfefferAcross_le_ofReal_mul (Real.exp_pos _) (fun u v => (hω n hn' u v).1) _ _ _),
      mul_le_exp_two_mul hN2
        (pfefferAcross_le_ofReal_mul (Real.exp_pos _) (fun u v => (hω n hn' u v).2) _ _ _)⟩
  · refine hX2.of_ae_comparison (E := fun n : ℕ => {ω | ∀ z, |f ω z| ≤ n})
      (L := fun n : ℕ => Real.exp (2 * (|ξ| * n))) (fun n => Real.exp_pos _) hev ?_
    filter_upwards [hcmp] with ω hω n hn r _
    have hn' : ∀ z, |f ω z| ≤ (n : ℝ) := hn
    obtain ⟨hN1, hN2⟩ := pfefferNormalization_bounds (ξ := ξ) (hcirc := hcirc)
      (c := fun r => r ^ (ξ * lqgQ γ)) hn' r
    exact ⟨mul_le_exp_two_mul hN1
        (pfefferAround_le_ofReal_mul (Real.exp_pos _) (fun u v => (hω n hn' u v).1) _ _ _),
      mul_le_exp_two_mul hN2
        (pfefferAround_le_ofReal_mul (Real.exp_pos _) (fun u v => (hω n hn' u v).2) _ _ _)⟩

/-- **Pfeffer's weak LQG metric axioms for a whole-plane GFF plus a bounded continuous function.** For a `γ`-LQG
metric `𝔇` with Weyl exponent `ξ`, a whole-plane GFF `h^ℂ` and a random continuous function `f`, measurable at every
point and almost surely globally bounded, the field `h^ℂ + f` satisfies the codomain condition and Axioms I–V of
Definition 1.6, Axiom V with the scaling constants `c_r = r^{ξQ}`. -/
theorem IsLQGMetric.boundedContinuousShift_pfefferWeakAxioms {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ x, Measurable fun ω => f ω x)
    (hbd : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ z, |f ω z| ≤ K) :
    PfefferWeakAxioms P ξ 𝔇 hC hcirc f :=
  h𝔇.continuousShift_pfefferWeakAxioms_of_axiomVScale h hf hfm
    ⟨_, h𝔇.boundedContinuousShift_pfefferAxiomVScale h hf hfm hbd⟩

end HarmonicBalls
