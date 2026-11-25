import HarmonicBalls.Proofs.Potential.ReflectedClockResolventSymmetry

/-!
# A bound for the potential of the clock

Let `A` be a clock of reflected Brownian motion in `K₀`, unbounded from every start, whose Revuz
measure `ν` (carried by `K₀`, without atoms in `K₀`) has mass at most `m` and closed-ball bounds
`ν(B̄(y, ρ)) ≤ A' ρ^{β'}` at the points `y ∈ K₀`. Then:

* `E_y ∫_{(0,1]} dA ≤ L` for every `y ∈ K₀` (`exists_lintegral_clockOccupation_window_le`): by the
  occupation identity from every start, `E_y ∫_{(0,1]} dA = ∫_0^1 ∫ k_s(y, z) ν(dz) ds`, and for
  `s ≤ 1` the Neumann kernel is dominated by a Gaussian of twice the variance
  (`squareNeumannKernel_le_heat`, from the image bounds of `ReflectedGreenPotentialBound.lean`),
  hence by `C s^{θ-1} |z - y|^{-2θ}`; the Riesz potential `∫ |y - z|^{-2θ} ν(dz)` is bounded by
  the ball bounds (`lintegral_norm_sub_rpow_neg_le`).
* `E_x ∫_{(n,n+1]} dA ≤ L` for every `n` (Markov property at time `n` and `∫ k_n(x, ·) = 1`), so
  the potential `G_β 1(x) = E_x ∫_0^∞ e^{-β s} dA_s ≤ L ∑_n e^{-β n}` is bounded on `K₀` for
  `β > 0` (`exists_clockGreen_one_le`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The interval Neumann kernel is dominated by a Gaussian density of twice the variance. -/
theorem intervalNeumannKernel_le_gaussianPDF {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) {s : ℝ≥0} (hs0 : s ≠ 0) (hs1 : s ≤ 1) :
    intervalNeumannKernel s u v ≤
      2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum * gaussianPDF u (2 * s) v := by
  rw [intervalNeumannKernel]
  calc ∑' n : ℤ, (gaussianPDF u s (v + 2 * n) + gaussianPDF u s (2 * n - v))
      = ∑' n : ℤ, (gaussianPDF (u - 2 * n) s v + gaussianPDF (2 * n - u) s v) := by
        congr 1
        funext n
        rw [gaussianPDF_congr_sq s (show (v + 2 * n - u) ^ 2 = (v - (u - 2 * n)) ^ 2 by ring),
          gaussianPDF_congr_sq s (show (2 * n - v - u) ^ 2 = (v - (2 * n - u)) ^ 2 by ring)]
    _ ≤ ∑' n : ℤ, 2 * ENNReal.ofReal (Real.sqrt 2) * gaussianPDF u (2 * s) v *
          ENNReal.ofReal (Real.exp (2 - |(n : ℝ)|)) :=
        ENNReal.tsum_le_tsum fun n => gaussianPDF_image_add_le hu hv hs0 hs1 n
    _ = 2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum * gaussianPDF u (2 * s) v := by
        rw [ENNReal.tsum_mul_left, foldLatticeSum]
        ring

/-- **Gaussian bound for the Neumann kernel of the square**: for `y, z ∈ K₀` and `0 < s ≤ 1`,
`k_s(y, z) ≤ (2 √2 S)² (4π s)⁻¹ e^{-|z - y|²/(4 s)}`. -/
theorem squareNeumannKernel_le_heat {y z : ℂ} (hy : y ∈ closedSquare 0 1)
    (hz : z ∈ closedSquare 0 1) {s : ℝ≥0} (hs0 : s ≠ 0) (hs1 : s ≤ 1) :
    squareNeumannKernel s y z ≤ (2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum) ^ 2 *
      ENNReal.ofReal ((2 * Real.pi * (2 * s))⁻¹ * Real.exp (-‖z - y‖ ^ 2 / (2 * (2 * s)))) := by
  have hy' : y.re ∈ Icc (0 : ℝ) 1 ∧ y.im ∈ Icc (0 : ℝ) 1 := by
    simpa [closedSquare, Complex.mem_reProdIm] using hy
  have hz' : z.re ∈ Icc (0 : ℝ) 1 ∧ z.im ∈ Icc (0 : ℝ) 1 := by
    simpa [closedSquare, Complex.mem_reProdIm] using hz
  have hs0' : 0 < (s : ℝ) := lt_of_le_of_ne s.coe_nonneg (by exact_mod_cast (Ne.symm hs0))
  rw [squareNeumannKernel]
  calc intervalNeumannKernel s y.re z.re * intervalNeumannKernel s y.im z.im
      ≤ (2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum * gaussianPDF y.re (2 * s) z.re) *
          (2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum * gaussianPDF y.im (2 * s) z.im) :=
        mul_le_mul' (intervalNeumannKernel_le_gaussianPDF hy'.1 hz'.1 hs0 hs1)
          (intervalNeumannKernel_le_gaussianPDF hy'.2 hz'.2 hs0 hs1)
    _ = (2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum) ^ 2 *
          (gaussianPDF y.re (2 * s) z.re * gaussianPDF y.im (2 * s) z.im) := by ring
    _ = _ := by
        congr 1
        rw [gaussianPDF_def, gaussianPDF_def, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
        congr 1
        simp only [gaussianPDFReal_def, NNReal.coe_mul, NNReal.coe_ofNat]
        set w : ℝ := 2 * Real.pi * (2 * s) with hw
        have hw0 : 0 < w := by positivity
        have hn : ‖z - y‖ ^ 2 = (z.re - y.re) ^ 2 + (z.im - y.im) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.sub_re, Complex.sub_im]
          ring
        rw [hn]
        have hsq : (Real.sqrt w)⁻¹ * (Real.sqrt w)⁻¹ = w⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt hw0.le]
        calc (Real.sqrt w)⁻¹ * Real.exp (-(z.re - y.re) ^ 2 / (2 * (2 * s))) *
              ((Real.sqrt w)⁻¹ * Real.exp (-(z.im - y.im) ^ 2 / (2 * (2 * s))))
            = ((Real.sqrt w)⁻¹ * (Real.sqrt w)⁻¹) * (Real.exp (-(z.re - y.re) ^ 2 / (2 * (2 * s))) *
                Real.exp (-(z.im - y.im) ^ 2 / (2 * (2 * s)))) := by ring
          _ = w⁻¹ * Real.exp (-((z.re - y.re) ^ 2 + (z.im - y.im) ^ 2) / (2 * (2 * s))) := by
            rw [hsq, ← Real.exp_add]
            congr 2
            ring

/-- The Neumann kernel at times `0 < s ≤ 1` is dominated by `K (2π)⁻¹ 2^θ s^{θ-1} |y - z|^{-2θ}`
off the diagonal. -/
theorem squareNeumannKernel_le_rpow {y z : ℂ} (hy : y ∈ closedSquare 0 1)
    (hz : z ∈ closedSquare 0 1) (hyz : z ≠ y) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    squareNeumannKernel s.toNNReal y z ≤ (2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum) ^ 2 *
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1)) *
        ENNReal.ofReal (‖y - z‖ ^ (-(2 * θ))) := by
  have hs0 : s.toNNReal ≠ 0 := (Real.toNNReal_pos.mpr hs.1).ne'
  have hs1 : s.toNNReal ≤ 1 := by
    rw [Real.toNNReal_le_one]
    exact hs.2
  have hcoe : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.1.le
  have h2s : 0 < 2 * s := by linarith [hs.1]
  refine (squareNeumannKernel_le_heat hy hz hs0 hs1).trans ?_
  rw [hcoe]
  refine (mul_le_mul' le_rfl ((ofReal_heatDensity_le hθ0 hθ1 h2s (z - y)).trans ?_)).trans_eq
    (mul_assoc _ _ _).symm
  have hpos : 0 < ‖z - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hyz)
  rw [ENNReal.ofReal_rpow_of_pos hpos, norm_sub_rev]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity)))
    le_rfl
  exact Real.rpow_le_rpow_of_nonpos hs.1 (by linarith [hs.1]) (by linarith)

/-- `∫_0^1 C s^{θ-1} ds = C / θ`. -/
theorem setLIntegral_Ioc_rpow_sub_one {θ : ℝ} (hθ0 : 0 < θ) {C : ℝ} (hC : 0 ≤ C) :
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (C * s ^ (θ - 1)) = ENNReal.ofReal (C * (1 / θ)) := by
  have hint : IntervalIntegrable (fun s : ℝ => C * s ^ (θ - 1)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hint)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => by
      have := hs.1
      positivity)), ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : (-1 : ℝ) < θ - 1))]
  congr 1
  rw [show θ - 1 + 1 = θ by ring, Real.zero_rpow hθ0.ne', sub_zero, Real.one_rpow]

/-- Occupation integrals from every start as integrals against the occupation measure. -/
theorem lintegral_clockOccupation_eq_lintegral_bind {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) {F : ℝ × ℂ → ℝ≥0∞} (hF : Measurable F) (x : ℂ) :
    ∫⁻ b, clockOccupation A F b ∂reflectedPlanarBrownianMotion 0 1 x =
      ∫⁻ q, F q ∂((reflectedPlanarBrownianMotion 0 1 x).bind (pathOccupationMeasure A)) := by
  rw [Measure.lintegral_bind (measurable_pathOccupationMeasure hA).aemeasurable hF.aemeasurable]
  exact lintegral_congr fun b => (lintegral_pathOccupationMeasure hA hF b).symm

/-- **The clock on the time window `(0, 1]`** has mean at most `L` from every start of `K₀`. -/
theorem exists_lintegral_clockOccupation_window_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) [IsFiniteMeasure (unitSquareRevuzMeasure A)]
    (hνK : unitSquareRevuzMeasure A (closedSquare 0 1)ᶜ = 0)
    (hatom : ∀ y ∈ closedSquare 0 1, unitSquareRevuzMeasure A {y} = 0)
    {m A' β' : ℝ} (hm : 0 ≤ m) (hA' : 0 ≤ A') (hβ' : 0 < β')
    (hmass : unitSquareRevuzMeasure A univ ≤ ENNReal.ofReal m)
    (hball : ∀ y ∈ closedSquare 0 1, ∀ ρ : ℝ, 0 < ρ →
      unitSquareRevuzMeasure A (closedBall y ρ) ≤ ENNReal.ofReal (A' * ρ ^ β')) :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ ∀ y ∈ closedSquare 0 1,
      ∫⁻ b, clockOccupation A (windowWeight (Ioc 0 1) fun _ => 1) b
        ∂reflectedPlanarBrownianMotion 0 1 y ≤ L := by
  set ν := unitSquareRevuzMeasure A with hν
  set θ : ℝ := min (β' / 4) 1 with hθ
  have hθ0 : 0 < θ := lt_min (by positivity) one_pos
  have hθ1 : θ ≤ 1 := min_le_right _ _
  have hθβ : 2 * θ < β' := by
    have := min_le_left (β' / 4) 1
    linarith
  set K := (2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum) ^ 2 with hK
  set C : ℝ := (2 * Real.pi)⁻¹ * 2 ^ θ with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨K * ENNReal.ofReal (C * (1 / θ)) * ENNReal.ofReal (m + A' * (2 * θ / (β' - 2 * θ))),
    ?_, fun y hy => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) foldLatticeSum_lt_top.ne))
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hK0 := ae_mem_closedSquare_of_compl_eq_zero hνK
  have hne : ∀ᵐ z ∂ν, z ≠ y := by
    rw [ae_iff]
    have hset : {a : ℂ | ¬a ≠ y} = {y} := by
      ext a
      simp
    rw [hset]
    exact hatom y hy
  set R := ∫⁻ z, ENNReal.ofReal (‖y - z‖ ^ (-(2 * θ))) ∂ν with hR
  have hRle : R ≤ ENNReal.ofReal (m + A' * (2 * θ / (β' - 2 * θ))) :=
    lintegral_norm_sub_rpow_neg_le (by linarith) hθβ hm hA' hmass (hball y hy)
  have hκ : Measurable fun q : ℝ × ℂ => squareNeumannKernel q.1.toNNReal y q.2 :=
    measurable_squareNeumannKernel_uncurry.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))
  have hW : Measurable (windowWeight (Ioc (0 : ℝ) 1) fun _ : ℂ => (1 : ℝ≥0∞)) :=
    measurable_windowWeight measurableSet_Ioc measurable_const
  rw [lintegral_clockOccupation_eq_lintegral_bind hA.measurable hW,
    bind_pathOccupationMeasure_eq hA hU hνK hy, lintegral_withDensity_eq_lintegral_mul _ hκ hW,
    lintegral_prod _ (hκ.mul hW).aemeasurable]
  have hpt : ∀ s, ∫⁻ z, ((fun q : ℝ × ℂ => squareNeumannKernel q.1.toNNReal y q.2) *
      windowWeight (Ioc (0 : ℝ) 1) fun _ : ℂ => (1 : ℝ≥0∞)) (s, z) ∂ν ≤
      (Ioc (0 : ℝ) 1).indicator (fun s => K * ENNReal.ofReal (C * s ^ (θ - 1)) * R) s := by
    intro s
    by_cases hs : s ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hs, hR, ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
          foldLatticeSum_lt_top.ne)) ENNReal.ofReal_ne_top)]
      refine lintegral_mono_ae ((hK0.and hne).mono fun z hz => ?_)
      simp only [Pi.mul_apply, windowWeight_apply, indicator_of_mem hs, mul_one]
      exact squareNeumannKernel_le_rpow hy hz.1 hz.2 hθ0 hθ1 hs
    · rw [indicator_of_notMem hs]
      refine le_of_eq ((lintegral_congr fun z => ?_).trans lintegral_zero)
      simp only [Pi.mul_apply, windowWeight_apply, indicator_of_notMem hs, mul_zero]
  calc ∫⁻ s, ∫⁻ z, ((fun q : ℝ × ℂ => squareNeumannKernel q.1.toNNReal y q.2) *
        windowWeight (Ioc (0 : ℝ) 1) fun _ : ℂ => (1 : ℝ≥0∞)) (s, z) ∂ν
          ∂volume.restrict (Ioi (0 : ℝ))
      ≤ ∫⁻ s, (Ioc (0 : ℝ) 1).indicator (fun s => K * ENNReal.ofReal (C * s ^ (θ - 1)) * R) s
          ∂volume.restrict (Ioi (0 : ℝ)) := lintegral_mono hpt
    _ ≤ ∫⁻ s, (Ioc (0 : ℝ) 1).indicator (fun s => K * ENNReal.ofReal (C * s ^ (θ - 1)) * R) s :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ s in Ioc (0 : ℝ) 1, K * ENNReal.ofReal (C * s ^ (θ - 1)) * R :=
        lintegral_indicator measurableSet_Ioc _
    _ = K * ENNReal.ofReal (C * (1 / θ)) * R := by
        rw [lintegral_mul_const' _ _ (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRle),
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
            (by simp) ENNReal.ofReal_ne_top) foldLatticeSum_lt_top.ne)),
          setLIntegral_Ioc_rpow_sub_one hθ0 hC0]
    _ ≤ _ := mul_le_mul' le_rfl hRle

/-- The occupation measure of a set as a mean occupation integral. -/
theorem bind_pathOccupationMeasure_apply {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (x : ℂ) {S : Set (ℝ × ℂ)} (hS : MeasurableSet S) :
    (reflectedPlanarBrownianMotion 0 1 x).bind (pathOccupationMeasure A) S =
      ∫⁻ b, clockOccupation A (S.indicator 1) b ∂reflectedPlanarBrownianMotion 0 1 x := by
  rw [Measure.bind_apply hS (measurable_pathOccupationMeasure hA).aemeasurable]
  refine lintegral_congr fun b => ?_
  rw [← lintegral_indicator_one hS, lintegral_pathOccupationMeasure hA (measurable_one.indicator hS)]

/-- `∫_{K₀} k_s(x, y) dy = 1` for `s ≠ 0`. -/
theorem setLIntegral_squareNeumannKernel_eq_one (x : ℂ) {s : ℝ≥0} (hs : s ≠ 0) :
    ∫⁻ y in closedSquare 0 1, squareNeumannKernel s x y = 1 := by
  have h := lintegral_reflected_eval_eq_neumannKernel (Φ := fun _ : ℂ => (1 : ℝ≥0∞))
    measurable_const x hs
  simp only [one_mul, lintegral_const, measure_univ, mul_one] at h
  exact h.symm

/-- **The clock on each window `(n, n + 1]`** has mean at most `L` from every start of `K₀`, if it
has on `(0, 1]`: Markov property at time `n`. -/
theorem lintegral_clockOccupation_window_nat_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) {L : ℝ≥0∞}
    (hL : ∀ y ∈ closedSquare 0 1, ∫⁻ b, clockOccupation A (windowWeight (Ioc 0 1) fun _ => 1) b
      ∂reflectedPlanarBrownianMotion 0 1 y ≤ L)
    {x : ℂ} (hx : x ∈ closedSquare 0 1) (n : ℕ) :
    ∫⁻ b, clockOccupation A (windowWeight (Ioc (n : ℝ) (n + 1)) fun _ => 1) b
      ∂reflectedPlanarBrownianMotion 0 1 x ≤ L := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hL x hx
  have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hshift := ae_clockOccupation_windowWeight_shift hA hx (hU x hx) (n : ℝ≥0) 1
  have hΨ : Measurable (clockOccupation A (windowWeight (Ioc 0 1) fun _ : ℂ => (1 : ℝ≥0∞))) :=
    measurable_clockOccupation hA.measurable
      (measurable_windowWeight measurableSet_Ioc measurable_const)
  have hk : Measurable fun y => squareNeumannKernel (n : ℝ≥0) x y :=
    (measurable_squareNeumannKernel _).comp (measurable_const.prodMk measurable_id)
  calc ∫⁻ b, clockOccupation A (windowWeight (Ioc (n : ℝ) (n + 1)) fun _ => 1) b
        ∂reflectedPlanarBrownianMotion 0 1 x
      = ∫⁻ b, clockOccupation A (windowWeight (Ioc 0 1) fun _ => 1)
          (ContinuousPath.shift (n : ℝ≥0) b) ∂reflectedPlanarBrownianMotion 0 1 x := by
        refine lintegral_congr_ae (hshift.mono fun b hb => ?_)
        have h := hb (fun _ => 1) measurable_const
        simp only [NNReal.coe_natCast] at h
        exact h
    _ = ∫⁻ y in closedSquare 0 1, (∫⁻ b, clockOccupation A (windowWeight (Ioc 0 1) fun _ => 1) b
          ∂reflectedPlanarBrownianMotion 0 1 y) * squareNeumannKernel (n : ℝ≥0) x y :=
        lintegral_shift_eq_neumannKernel hΨ x hn'
    _ ≤ ∫⁻ y in closedSquare 0 1, L * squareNeumannKernel (n : ℝ≥0) x y :=
        setLIntegral_mono' (isCompact_closedSquare 0 1).isClosed.measurableSet fun y hy =>
          mul_le_mul' (hL y hy) le_rfl
    _ = L := by
        rw [lintegral_const_mul _ hk, setLIntegral_squareNeumannKernel_eq_one x hn', mul_one]

/-- **The potential of `1` is bounded on `K₀`** for `β > 0`, if the clock on `(0, 1]` has bounded
mean: `G_β 1(x) ≤ L ∑_n e^{-β n}`. -/
theorem exists_clockGreen_one_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) [IsFiniteMeasure (unitSquareRevuzMeasure A)]
    (hνK : unitSquareRevuzMeasure A (closedSquare 0 1)ᶜ = 0) {L : ℝ≥0∞} (hLtop : L ≠ ⊤)
    (hL : ∀ y ∈ closedSquare 0 1, ∫⁻ b, clockOccupation A (windowWeight (Ioc 0 1) fun _ => 1) b
      ∂reflectedPlanarBrownianMotion 0 1 y ≤ L)
    {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x ∈ closedSquare 0 1, clockGreen A β (fun _ => 1) x ≤ C := by
  set r := ENNReal.ofReal (Real.exp (-β)) with hr
  have hr1 : r < 1 :=
    ENNReal.ofReal_lt_one.2 ((Real.exp_lt_exp.2 (neg_lt_zero.2 hβ)).trans_eq Real.exp_zero)
  refine ⟨L * ∑' n : ℕ, r ^ n, ?_, fun x hx => ?_⟩
  · rw [ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top hLtop (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hr1).ne')
  set M := (reflectedPlanarBrownianMotion 0 1 x).bind (pathOccupationMeasure A) with hM
  have hdw := measurable_discountWeight β
    (show Measurable fun _ : ℂ => (1 : ℝ≥0∞) from measurable_const)
  have hpos : ∀ᵐ q ∂M, 0 < q.1 := by
    rw [hM, bind_pathOccupationMeasure_eq hA hU hνK hx]
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    exact Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst
      (ae_restrict_mem measurableSet_Ioi)
  have hI : ∀ n : ℕ, MeasurableSet (Ioc (n : ℝ) (n + 1) ×ˢ (univ : Set ℂ)) := fun n =>
    measurableSet_Ioc.prod MeasurableSet.univ
  rw [clockGreen, lintegral_clockOccupation_eq_lintegral_bind hA.measurable hdw]
  calc ∫⁻ q, discountWeight β (fun _ => 1) q ∂M
      ≤ ∫⁻ q, ∑' n : ℕ, r ^ n * (Ioc (n : ℝ) (n + 1) ×ˢ (univ : Set ℂ)).indicator 1 q ∂M := by
        refine lintegral_mono_ae (hpos.mono fun q hq => ?_)
        have hc : 0 < ⌈q.1⌉₊ := Nat.ceil_pos.2 hq
        have hmem : q ∈ Ioc ((⌈q.1⌉₊ - 1 : ℕ) : ℝ) ((⌈q.1⌉₊ - 1 : ℕ) + 1) ×ˢ (univ : Set ℂ) := by
          refine ⟨⟨?_, ?_⟩, mem_univ _⟩
          · rw [Nat.cast_sub hc, Nat.cast_one]
            linarith [Nat.ceil_lt_add_one hq.le]
          · rw [Nat.cast_sub hc, Nat.cast_one]
            linarith [Nat.le_ceil q.1]
        refine le_trans ?_ (ENNReal.le_tsum (⌈q.1⌉₊ - 1))
        rw [indicator_of_mem hmem, Pi.one_apply, mul_one, hr,
          ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
        show ENNReal.ofReal (Real.exp (-(β * q.1))) * 1 ≤ _
        rw [mul_one]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have h1 : ((⌈q.1⌉₊ - 1 : ℕ) : ℝ) < q.1 := hmem.1.1
        nlinarith
    _ = ∑' n : ℕ, r ^ n * M (Ioc (n : ℝ) (n + 1) ×ˢ (univ : Set ℂ)) := by
        rw [lintegral_tsum fun n => ((measurable_one.indicator (hI n)).const_mul _).aemeasurable]
        congr 1
        funext n
        rw [lintegral_const_mul _ (measurable_one.indicator (hI n)), lintegral_indicator_one (hI n)]
    _ ≤ ∑' n : ℕ, r ^ n * L := by
        refine ENNReal.tsum_le_tsum fun n => mul_le_mul' le_rfl ?_
        rw [hM, bind_pathOccupationMeasure_apply hA.measurable x (hI n),
          indicator_prod_eq_windowWeight, indicator_univ]
        exact lintegral_clockOccupation_window_nat_le hA hU hL hx n
    _ = L * ∑' n : ℕ, r ^ n := by rw [ENNReal.tsum_mul_right, mul_comm]

end HarmonicBalls
