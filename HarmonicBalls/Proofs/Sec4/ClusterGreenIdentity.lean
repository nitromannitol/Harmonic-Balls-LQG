import HarmonicBalls.Proofs.Sec4.GreenBalayage
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole
import HarmonicBalls.Proofs.Sec4.ClusterSubharmonicBall
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic

/-!
# Lemma 4.3 (lemma:harmonic-ball, line 755): Step 2 and the assembly

* `clusterGreenPotentialIdentityStep_of`: `ClusterGreenPotentialIdentityStep` (lines 781-786, corrected by G5) from
  Step 1 (`ClusterHarmonicQuadratureStep`) and `GreenHarmonicCorrectionBalayageStep`.
  1. *Newtonian representation.* For `y ≠ z`, `∫_Λ N(x,y) μ(dx) = t N(z,y) - ũ(y)`, `ũ = 1_Λ u`: for `y ∈ B_R`
     from the Green representation of `u` on `B_R` and Step 1 applied to the harmonic part
     `x ↦ N(y,x) - G_{B_R}(y,x)`; for `y ∉ B_R` from Step 1 applied to `x ↦ N(y,x)`.
  2. *Harmonic correction.* Step 1 applied to `x ↦ N_ε(x,w)` (harmonic near `closure Λ` when `w` is far) gives the
     hypothesis of `GreenHarmonicCorrectionBalayageStep` for `m = μ|_Λ`; hence `G_O = N - H` with
     `∫_Λ H(x,y) μ(dx) = t H(z,y)`, and `∫_Λ G_O(x,y) μ(dx) = t G_O(z,y) - ũ(y)` for `y ∈ O \ {z}`.
  3. *Fubini* on `Λ × K` (`G_O` is bounded below on `closure Λ × K`, and the identity bounds the fibre integrals
     of `|G_O|` by `t |G_O(z,·)| + C ∈ L¹(ν)`).
* `clusterGreenPotentialIdentityStep_holds`, and **Lemma 4.3**: `clusterSubharmonicBall_proved` (given I2) and
  `clusterSubharmonicBall_of_literature`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Function ComplexConjugate InnerProductSpace

universe u

theorem measurable_uncurry_newtonKernel : Measurable (uncurry newtonKernel) := by
  have e : uncurry newtonKernel = fun p : ℂ × ℂ => -(2 * Real.pi)⁻¹ * Real.log ‖p.1 - p.2‖ := rfl
  rw [e]
  exact (Real.measurable_log.comp (measurable_fst.sub measurable_snd).norm).const_mul _

/-- **Lemma 4.3, Step 2** from Step 1 and the harmonic correction step. -/
theorem clusterGreenPotentialIdentityStep_of (hS1 : ClusterHarmonicQuadratureStep)
    (hB : GreenHarmonicCorrectionBalayageStep) : ClusterGreenPotentialIdentityStep := by
  intro μ hμ R βm βp hV Λ z t u hU O K ν hO hΛO hK hKO hν hνK hνz hGz
  obtain ⟨hR, ht, hΛo, hzΛ, hclR, -, hu0, hnn, -, hrep⟩ := id hU
  have hLc : IsCompact (closure Λ) := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure
    (hclR.trans ball_subset_closedBall)
  have hΛB : Λ ⊆ ball (0 : ℂ) R := subset_closure.trans hclR
  have hμΛ : μ Λ < ⊤ := (measure_mono subset_closure).trans_lt hLc.measure_lt_top
  have hm : IsFiniteMeasure (μ.restrict Λ) := isFiniteMeasure_restrict.2 hμΛ.ne
  have hmL : μ.restrict Λ (closure Λ)ᶜ = 0 := by
    rw [Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet,
      eq_empty_of_forall_notMem (s := (closure Λ)ᶜ ∩ Λ) fun x hx => hx.1 (subset_closure hx.2), measure_empty]
  have hsing : ∀ y, μ.restrict Λ {y} = 0 := by
    intro y
    rw [Measure.restrict_apply (measurableSet_singleton y)]
    by_cases hy : y ∈ Λ
    · exact measure_mono_null inter_subset_left (hV.measure_singleton (hΛB hy))
    · rw [eq_empty_of_forall_notMem (s := {y} ∩ Λ) fun x hx => hy (by rw [← mem_singleton_iff.1 hx.1]; exact hx.2),
        measure_empty]
  have hne : ∀ y, ∀ᵐ x ∂(μ.restrict Λ), x ≠ y := by
    intro y
    rw [ae_iff]
    simpa using hsing y
  have hmemΛ : ∀ᵐ x ∂(μ.restrict Λ), x ∈ Λ := ae_restrict_mem hΛo.measurableSet
  -- the regularization scale
  obtain ⟨δ, hδ, hδO⟩ := hLc.exists_cthickening_subset_open hO hΛO
  have hε : 0 < δ / 3 := by positivity
  have h3 : cthickening (3 * (δ / 3)) (closure Λ) ⊆ O := by
    rw [show 3 * (δ / 3) = δ by ring]
    exact hδO
  -- the hypothesis of the harmonic correction step, from Step 1
  have hbal : ∀ w : ℂ, (∀ x ∈ closure Λ, δ / 3 < ‖x - w‖) →
      ∫ x, regularizedNewtonKernel (δ / 3) x w ∂(μ.restrict Λ) = t * regularizedNewtonKernel (δ / 3) z w := by
    intro w hw
    have hO' : IsOpen {x : ℂ | δ / 3 < ‖x - w‖} :=
      isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
    have hq : HarmonicOnNhd (fun x => regularizedNewtonKernel (δ / 3) x w) {x : ℂ | δ / 3 < ‖x - w‖} := by
      intro x hx
      have hxw : x ≠ w := fun e => by
        have hx' : δ / 3 < ‖x - w‖ := hx
        rw [e, sub_self, norm_zero] at hx'
        linarith
      have hev : (fun x => regularizedNewtonKernel (δ / 3) x w) =ᶠ[𝓝 x] newtonKernel w := by
        filter_upwards [hO'.mem_nhds hx] with v hv
        rw [regularizedNewtonKernel_of_le_norm (le_of_lt hv), newtonKernel_comm]
      exact (harmonicAt_congr_nhds hev).2 (harmonicAt_newtonKernel hxw)
    obtain ⟨-, he⟩ := hS1 μ R Λ z t u hU _ _ hO' (fun x hx => hw x hx) hq
    exact he.symm
  obtain ⟨H, hHm, hHag, hHbd, hHid⟩ :=
    hB O (closure Λ) (μ.restrict Λ) z t (δ / 3) hO hLc hm hmL (subset_closure hzΛ) hε h3 hbal
  -- 1. the Newtonian representation of `ũ = 1_Λ u`
  have hNR : ∀ y, y ≠ z → IntegrableOn (fun x => newtonKernel x y) Λ μ ∧
      ∫ x in Λ, newtonKernel x y ∂μ = t * newtonKernel z y - Λ.indicator u y := by
    intro y hyz
    by_cases hyB : y ∈ ball (0 : ℂ) R
    · obtain ⟨hGi, hGe⟩ := hrep y hyB
      have hyR : ‖y‖ < R := mem_ball_zero_iff.1 hyB
      have hqO : IsOpen {x : ℂ | (R : ℂ) ^ 2 - conj y * x ≠ 0} :=
        isOpen_ne_fun (continuous_const.sub (continuous_const.mul continuous_id)) continuous_const
      have hqh : HarmonicOnNhd (greatestHarmonicMinorantBall R y) {x : ℂ | (R : ℂ) ^ 2 - conj y * x ≠ 0} :=
        fun x hx => harmonicAt_greatestHarmonicMinorantBall hx
      have hΛq : closure Λ ⊆ {x : ℂ | (R : ℂ) ^ 2 - conj y * x ≠ 0} := fun x hx =>
        norm_pos_iff.1 (norm_sub_conj_mul_pos hR hyR (mem_ball_zero_iff.1 (hclR hx)).le)
      obtain ⟨hqi, hqe⟩ := hS1 μ R Λ z t u hU _ _ hqO hΛq hqh
      have hae : (fun x => newtonKernel x y) =ᵐ[μ.restrict Λ]
          fun x => greenFunction (ball 0 R) y x + greatestHarmonicMinorantBall R y x := by
        filter_upwards [hne y, hmemΛ] with x hxy hx
        rw [greenFunction_ball_eq_sub hyB (hΛB hx) (Ne.symm hxy), newtonKernel_comm]
        ring
      refine ⟨(hGi.add hqi).congr hae.symm, ?_⟩
      rw [integral_congr_ae hae, integral_add hGi hqi, ← hqe]
      have hGe' : ∫ x in Λ, greenFunction (ball 0 R) y x ∂μ = t * greenFunction (ball 0 R) z y - u y := by
        linarith
      rw [hGe', greenFunction_ball_comm R z y, greenFunction_ball_eq_sub hyB (hΛB hzΛ) hyz]
      have hind : Λ.indicator u y = u y := by
        by_cases hyΛ : y ∈ Λ
        · rw [indicator_of_mem hyΛ]
        · rw [indicator_of_notMem hyΛ, hu0 y ⟨hyB, hyΛ⟩]
      rw [hind, newtonKernel_comm z y]
      ring
    · have hqh : HarmonicOnNhd (fun x => newtonKernel y x) (ball (0 : ℂ) R) :=
        fun x hx => harmonicAt_newtonKernel (fun e => hyB (e ▸ hx))
      obtain ⟨hqi, hqe⟩ := hS1 μ R Λ z t u hU _ _ isOpen_ball hclR hqh
      have he : (fun x => newtonKernel x y) = fun x => newtonKernel y x :=
        funext fun x => newtonKernel_comm x y
      have hind : Λ.indicator u y = 0 := indicator_of_notMem (fun h => hyB (hΛB h)) u
      refine ⟨he ▸ hqi, ?_⟩
      rw [he, ← hqe, hind, newtonKernel_comm z y, sub_zero]
  -- 2. the identity for each `y ∈ O \ {z}`
  have hHy : ∀ y ∈ O, Integrable (fun x => H x y) (μ.restrict Λ) := by
    intro y hy
    obtain ⟨C, hC⟩ := hHbd {y} isCompact_singleton (singleton_subset_iff.2 hy)
    refine Integrable.of_bound (hHm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable C ?_
    filter_upwards [hmemΛ] with x hx
    rw [Real.norm_eq_abs]
    exact hC x (subset_closure hx) y rfl
  have hGeq : ∀ y ∈ O, ∀ x ∈ closure Λ, x ≠ y → greenFunction O x y = newtonKernel x y - H x y := by
    intro y hy x hx hxy
    rw [greenFunction, ite_eq_left ⟨hΛO hx, hy, hxy⟩, hHag x hx y hy]
  have hID : ∀ y ∈ O, y ≠ z → Integrable (fun x => greenFunction O x y) (μ.restrict Λ) ∧
      ∫ x, greenFunction O x y ∂(μ.restrict Λ) = t * greenFunction O z y - Λ.indicator u y := by
    intro y hy hyz
    obtain ⟨hNi, hNe⟩ := hNR y hyz
    have hae : (fun x => greenFunction O x y) =ᵐ[μ.restrict Λ] fun x => newtonKernel x y - H x y := by
      filter_upwards [hne y, hmemΛ] with x hxy hx
      exact hGeq y hy x (subset_closure hx) hxy
    refine ⟨(hNi.sub (hHy y hy)).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_sub hNi (hHy y hy), hNe, hHid y hy,
      hGeq y hy z (subset_closure hzΛ) (Ne.symm hyz)]
    ring
  -- 3. Fubini on `Λ × K`
  have hνK' : ∀ᵐ y ∂ν, y ∈ K := by
    rw [ae_iff]
    simpa [compl_def] using hνK
  have hνz' : ∀ᵐ y ∂ν, y ≠ z := by
    rw [ae_iff]
    simpa using hνz
  have hprodL : ∀ᵐ p ∂((μ.restrict Λ).prod ν), p.1 ∈ closure Λ := by
    have h0 : ((μ.restrict Λ).prod ν) ((closure Λ)ᶜ ×ˢ univ) = 0 := by
      rw [Measure.prod_prod, hmL, zero_mul]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with p hp
    by_contra hc
    exact hp ⟨hc, mem_univ _⟩
  have hprodK : ∀ᵐ p ∂((μ.restrict Λ).prod ν), p.2 ∈ K := by
    have h0 : ((μ.restrict Λ).prod ν) (univ ×ˢ Kᶜ) = 0 := by
      rw [Measure.prod_prod, hνK, mul_zero]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with p hp
    by_contra hc
    exact hp ⟨mem_univ _, hc⟩
  -- measurability of `G_O` on `closure Λ × ℂ`
  classical
  have hset : MeasurableSet {p : ℂ × ℂ | p.2 ∈ O ∧ p.1 ≠ p.2} :=
    (measurable_snd hO.measurableSet).inter isClosed_diagonal.isOpen_compl.measurableSet
  have hΦ'm : Measurable fun p : ℂ × ℂ =>
      if p.2 ∈ O ∧ p.1 ≠ p.2 then newtonKernel p.1 p.2 - H p.1 p.2 else 0 :=
    Measurable.ite hset (measurable_uncurry_newtonKernel.sub hHm) measurable_const
  have hΦae : uncurry (greenFunction O) =ᵐ[(μ.restrict Λ).prod ν] fun p : ℂ × ℂ =>
      if p.2 ∈ O ∧ p.1 ≠ p.2 then newtonKernel p.1 p.2 - H p.1 p.2 else 0 := by
    filter_upwards [hprodL] with p hp
    simp only [uncurry]
    by_cases hc : p.2 ∈ O ∧ p.1 ≠ p.2
    · rw [ite_eq_left hc, hGeq p.2 hc.1 p.1 hp hc.2]
    · rw [ite_eq_right hc, greenFunction, ite_eq_right (fun h => hc ⟨h.2.1, h.2.2⟩)]
  have hΦmeas : AEStronglyMeasurable (uncurry (greenFunction O)) ((μ.restrict Λ).prod ν) :=
    hΦ'm.aestronglyMeasurable.congr hΦae.symm
  -- the lower bound of `G_O` on `closure Λ × K`
  obtain ⟨r, hr⟩ := (hK.union hLc).isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨CH, hCH⟩ := hHbd K hK hKO
  have hr0 : 0 ≤ r := by
    have := hr (Or.inr (subset_closure hzΛ))
    exact dist_nonneg.trans (mem_closedBall.1 this)
  have hD : 0 < 2 * r + 1 := by linarith
  set C₁ : ℝ := (2 * Real.pi)⁻¹ * |Real.log (2 * r + 1)| + |CH| with hC₁
  have hC₁0 : 0 ≤ C₁ := add_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) (abs_nonneg _)
  have hlow : ∀ x ∈ closure Λ, ∀ y ∈ K, -C₁ ≤ greenFunction O x y := by
    intro x hx y hy
    by_cases hxy : x = y
    · rw [hxy, greenFunction_self]
      linarith
    rw [hGeq y (hKO hy) x hx hxy]
    have hxr : ‖x‖ ≤ r := by simpa using hr (Or.inr hx)
    have hyr : ‖y‖ ≤ r := by simpa using hr (Or.inl hy)
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have hle : ‖x - y‖ ≤ 2 * r + 1 := by linarith [norm_sub_le x y]
    have hlog := Real.log_le_log hpos hle
    have hH := hCH x hx y hy
    rw [abs_le] at hH
    have hπ : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
    have h1 : -(2 * Real.pi)⁻¹ * |Real.log (2 * r + 1)| ≤ newtonKernel x y := by
      rw [newtonKernel, neg_mul, neg_mul, neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_left (hlog.trans (le_abs_self _)) hπ
    linarith [le_abs_self CH]
  have hfib : ∀ y ∈ K, y ≠ z → ∫ x, ‖greenFunction O x y‖ ∂(μ.restrict Λ) ≤
      t * |greenFunction O z y| + 2 * C₁ * (μ.restrict Λ).real univ := by
    intro y hy hyz
    obtain ⟨hi, he⟩ := hID y (hKO hy) hyz
    have hmono : ∫ x, ‖greenFunction O x y‖ ∂(μ.restrict Λ) ≤
        ∫ x, (greenFunction O x y + 2 * C₁) ∂(μ.restrict Λ) := by
      refine integral_mono_ae hi.norm (hi.add (integrable_const _)) ?_
      filter_upwards [hmemΛ] with x hx
      have := hlow x (subset_closure hx) y hy
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    rw [integral_add hi (integrable_const _), he, integral_const, smul_eq_mul] at hmono
    have hũ : 0 ≤ Λ.indicator u y := by
      by_cases hyΛ : y ∈ Λ
      · rw [indicator_of_mem hyΛ]
        exact hnn y (hΛB hyΛ) hyz
      · rw [indicator_of_notMem hyΛ]
    have := mul_le_mul_of_nonneg_left (le_abs_self (greenFunction O z y)) ht.le
    linarith
  have hInt : Integrable (uncurry (greenFunction O)) ((μ.restrict Λ).prod ν) := by
    refine (integrable_prod_iff' hΦmeas).2 ⟨?_, ?_⟩
    · filter_upwards [hνK', hνz'] with y hy hyz
      exact (hID y (hKO hy) hyz).1
    · refine Integrable.mono' ((hGz.abs.const_mul t).add (integrable_const (2 * C₁ * (μ.restrict Λ).real univ)))
        ?_ ?_
      · exact (hΦmeas.norm.prod_swap).integral_prod_right'
      · filter_upwards [hνK', hνz'] with y hy hyz
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
        exact hfib y hy hyz
  have hfibeq : (fun y => ∫ x, greenFunction O x y ∂(μ.restrict Λ)) =ᵐ[ν]
      fun y => t * greenFunction O z y - Λ.indicator u y := by
    filter_upwards [hνK', hνz'] with y hy hyz
    exact (hID y (hKO hy) hyz).2
  have hũi : Integrable (Λ.indicator u) ν := by
    have h := (hGz.const_mul t).sub hInt.integral_prod_right
    refine h.congr ?_
    filter_upwards [hfibeq] with y hy
    simp only [uncurry, Pi.sub_apply] at hy ⊢
    rw [hy]
    ring
  refine ⟨hInt.integral_prod_left, hũi, ?_⟩
  have hswap := integral_integral_swap (f := greenFunction O) hInt
  calc ∫ x in Λ, greenPotential O ν x ∂μ = ∫ x, ∫ y, greenFunction O x y ∂ν ∂(μ.restrict Λ) := rfl
    _ = ∫ y, ∫ x, greenFunction O x y ∂(μ.restrict Λ) ∂ν := hswap
    _ = ∫ y, (t * greenFunction O z y - Λ.indicator u y) ∂ν := integral_congr_ae hfibeq
    _ = t * greenPotential O ν z - ∫ y, Λ.indicator u y ∂ν := by
      rw [integral_sub (hGz.const_mul t) hũi, integral_const_mul]
      rfl

/-- **Lemma 4.3, Step 2** (`ClusterGreenPotentialIdentityStep`). -/
theorem clusterGreenPotentialIdentityStep_holds : ClusterGreenPotentialIdentityStep :=
  clusterGreenPotentialIdentityStep_of clusterHarmonicQuadratureStep_holds greenHarmonicCorrectionBalayageStep_holds

/-- **Lemma 4.3** (lemma:harmonic-ball), with I2 (`LQGVolumeGrowthAllScalesStmt`) as the only hypothesis. -/
theorem clusterSubharmonicBall_proved (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ClusterSubharmonicBallStmt.{u} :=
  clusterSubharmonicBall_of_steps hI2 greenFunctionBall (leastSupersolutionMem_proved hI2)
    (clusterOpenLaplacian_proved hI2) (clusterConservationOfMass_proved hI2) greenRepresentationBallStep_holds
    clusterHarmonicQuadratureStep_holds clusterGreenPotentialIdentityStep_holds
    greenFunctionIntegrableAwayFromPoleStep_holds

section FromLiterature

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
  (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)

include hDG hAff hCC hW hE hN

/-- **Lemma 4.3** (lemma:harmonic-ball) from the staged literature inputs. -/
theorem clusterSubharmonicBall_of_literature : ClusterSubharmonicBallStmt.{u} :=
  clusterSubharmonicBall_proved (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN)

end FromLiterature

end HarmonicBalls
