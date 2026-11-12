import HarmonicBalls.FirstPass.Phase2.CampbellKernel
import HarmonicBalls.FirstPass.Phase2.CampbellProductLimit

/-!
# The marked Campbell identity (Duplantier-Miller-Sheffield, Lemma A.10, whole-plane clause)

For a whole-plane GFF `h`, `0 < γ < 2`, and its `γ`-LQG measure `μ` (insertion `α = 0`), the rooted measure
`P.bind (ω ↦ (μ_ω|_{B₁}).map (z ↦ (h(ω), z)))` and the DMS-shifted measure
`(Leb|_{B₁}).bind (z ↦ P.map (ω ↦ (h(ω) + f_z + κ, z)))` on the observation space pairing × mark coincide
(Duplantier-Sheffield, §3.3; Duplantier-Miller-Sheffield, Lemma A.10). Both are finite measures; they agree on the
open cylinders `{(T φ_i)_i ∈ A} ×ˢ V` (`A ⊆ ℝⁿ`, `V ⊆ ℂ` open), which form a generating π-system: approximate
`1_A` and `1_{V ∩ B₁}` from below by continuous cutoffs and pass to the limit in the Campbell identity for product
tests by monotone convergence.

## Main results

* `CampbellKernel.exists_cutoff_iSup_eq_indicator`: continuous cutoffs `0 ≤ F_j ≤ 1` increasing to the indicator of
  an open set, supported inside it.
* `CampbellKernel.generateFrom_openCylinders`, `CampbellKernel.isPiSystem_openCylinders`: the open cylinders generate
  the σ-algebra of the observation space and form a π-system.
* `CampbellKernel.markedLeftMeas_eq_markedRightMeas`: the rooted measure equals the DMS-shifted measure.
* `dmsLemmaA10WholePlaneMarkedSub_holds`: the marked whole-plane form of Lemma A.10, `DMSLemmaA10WholePlaneMarkedSub`.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HarmonicBalls

namespace CampbellKernel

attribute [local instance] markObsSigma

/-- **Continuous cutoffs of an open set.** For an open set `A` of a pseudometric space there are continuous
`0 ≤ F_j ≤ 1`, nondecreasing in `j`, with `tsupport F_j ⊆ A` and `⨆_j F_j = 1_A`. -/
theorem exists_cutoff_iSup_eq_indicator {X : Type*} [PseudoMetricSpace X] {A : Set X} (hA : IsOpen A) :
    ∃ F : ℕ → X → ℝ, (∀ j, Continuous (F j)) ∧ (∀ j x, 0 ≤ F j x) ∧ (∀ j x, F j x ≤ 1) ∧
      (∀ x, Monotone fun j => F j x) ∧ (∀ x, ⨆ j, ENNReal.ofReal (F j x) = A.indicator 1 x) ∧
      ∀ j, tsupport (F j) ⊆ A := by
  rcases (Aᶜ).eq_empty_or_nonempty with hAc | hAc
  · have hAu : A = univ := compl_empty_iff.1 hAc
    refine ⟨fun _ _ => 1, fun _ => continuous_const, fun _ _ => zero_le_one, fun _ _ => le_rfl,
      fun _ => monotone_const, fun x => ?_, fun _ => hAu ▸ subset_univ _⟩
    simp [hAu]
  · refine ⟨fun j x => max 0 (min 1 ((j : ℝ) * infDist x Aᶜ - 1)), fun j => ?_, fun j x => le_max_left _ _,
      fun j x => max_le zero_le_one (min_le_left _ _), fun x i j hij => ?_, fun x => ?_, fun j => ?_⟩
    · exact continuous_const.max (continuous_const.min
        ((continuous_const.mul (continuous_infDist_pt _)).sub continuous_const))
    · exact max_le_max le_rfl (min_le_min le_rfl (sub_le_sub_right
        (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) infDist_nonneg) _))
    · by_cases hx : x ∈ A
      · have hd : 0 < infDist x Aᶜ :=
          (hA.isClosed_compl.notMem_iff_infDist_pos hAc).1 fun h => h hx
        obtain ⟨j, hj⟩ := exists_nat_ge (2 / infDist x Aᶜ)
        have hj2 : 2 ≤ (j : ℝ) * infDist x Aᶜ := by
          rwa [div_le_iff₀ hd] at hj
        have hj1 : max 0 (min 1 ((j : ℝ) * infDist x Aᶜ - 1)) = 1 := by
          rw [min_eq_left (by linarith), max_eq_right zero_le_one]
        simp only [indicator_of_mem hx, Pi.one_apply]
        refine le_antisymm (iSup_le fun i => ENNReal.ofReal_le_one.2 (max_le zero_le_one (min_le_left _ _))) ?_
        exact le_iSup_of_le j (by simp [hj1])
      · have hd : infDist x Aᶜ = 0 := infDist_zero_of_mem hx
        have h0 : ∀ j : ℕ, max 0 (min 1 ((j : ℝ) * infDist x Aᶜ - 1)) = 0 := fun j => by
          rw [hd, mul_zero, zero_sub]
          exact max_eq_left ((min_le_right _ _).trans (by norm_num))
        simp [indicator_of_notMem hx, h0]
    · have hT : IsClosed {x : X | 1 ≤ (j : ℝ) * infDist x Aᶜ} :=
        isClosed_le continuous_const (continuous_const.mul (continuous_infDist_pt _))
      refine (closure_minimal (fun x hx => ?_) hT).trans fun x hx => ?_
      · by_contra h
        have h' : (j : ℝ) * infDist x Aᶜ < 1 := not_le.1 h
        exact hx (max_eq_left ((min_le_right _ _).trans (by linarith)))
      · by_contra h
        have h1 : 1 ≤ (j : ℝ) * infDist x Aᶜ := hx
        rw [infDist_zero_of_mem h, mul_zero] at h1
        exact absurd h1 (by norm_num)

/-- Evaluation of the pairing at a test function is measurable on the observation space. -/
theorem measurable_eval_markObs {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    Measurable fun x : MarkObs => x.1 φ := by
  have h : Measurable[pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ] fun T : (ℂ → ℝ) → ℝ => T φ :=
    Measurable.of_comap_le (le_iSup₂ (f := fun φ' (_ : IsTestFunction univ φ') =>
      MeasurableSpace.comap (fun T : (ℂ → ℝ) → ℝ => T φ') inferInstance) φ hφ)
  exact h.comp measurable_fst

/-- The open cylinders `{x | (x.1 φ_i)_i ∈ A, x.2 ∈ V}` of the observation space, for test functions `φ_i` and open
sets `A ⊆ ℝⁿ`, `V ⊆ ℂ`. -/
def openCylinders : Set (Set MarkObs) :=
  {S | ∃ (n : ℕ) (φ : Fin n → ℂ → ℝ) (A : Set (Fin n → ℝ)) (V : Set ℂ),
    (∀ i, IsTestFunction univ (φ i)) ∧ IsOpen A ∧ IsOpen V ∧ S = {x | (fun i => x.1 (φ i)) ∈ A ∧ x.2 ∈ V}}

/-- The open cylinders form a π-system. -/
theorem isPiSystem_openCylinders : IsPiSystem openCylinders := by
  rintro _ ⟨n, φ, A, V, hφ, hA, hV, rfl⟩ _ ⟨m, ψ, B, W, hψ, hB, hW, rfl⟩ -
  refine ⟨n + m, Fin.append φ ψ,
    {y | (fun i => y (Fin.castAdd m i)) ∈ A ∧ (fun i => y (Fin.natAdd n i)) ∈ B}, V ∩ W, ?_, ?_, hV.inter hW, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact hφ j
    · simp only [Fin.append_right]
      exact hψ j
  · exact (hA.preimage (continuous_pi fun i => continuous_apply _)).inter
      (hB.preimage (continuous_pi fun i => continuous_apply _))
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Fin.append_left, Fin.append_right]
    tauto

/-- The open cylinders generate the σ-algebra of the observation space (pairing σ-algebra ⊗ Borel). -/
theorem generateFrom_openCylinders : MeasurableSpace.generateFrom openCylinders = markObsSigma := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨n, φ, A, V, hφ, hA, hV, rfl⟩
    exact ((measurable_pi_iff.mpr fun i => measurable_eval_markObs (hφ i)) hA.measurableSet).inter
      (measurable_snd hV.measurableSet)
  · show MeasurableSpace.comap Prod.fst (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ) ⊔
      MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace ℂ) ≤ _
    refine sup_le ?_ ?_
    · unfold pairingSigmaAlgebra
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun φ => ?_
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun hφ => ?_
      rw [MeasurableSpace.comap_comp]
      have hm : Measurable[MeasurableSpace.generateFrom openCylinders] fun x : MarkObs => x.1 φ :=
        @measurable_generateFrom MarkObs ℝ (MeasurableSpace.generateFrom openCylinders) {s | IsOpen s} _
          fun U hU => MeasurableSpace.measurableSet_generateFrom ⟨1, fun _ => φ, {y | y 0 ∈ U}, univ,
            fun _ => hφ, IsOpen.preimage (continuous_apply 0) (show IsOpen U from hU), isOpen_univ, by ext x; simp⟩
      exact measurable_iff_comap_le.1 hm
    · have hm : Measurable[MeasurableSpace.generateFrom openCylinders] (Prod.snd : MarkObs → ℂ) :=
        @measurable_generateFrom MarkObs ℂ (MeasurableSpace.generateFrom openCylinders) {s | IsOpen s} _
          fun V hV => MeasurableSpace.measurableSet_generateFrom ⟨0, Fin.elim0, univ, V,
            fun i => i.elim0, isOpen_univ, hV, by ext x; simp⟩
      exact measurable_iff_comap_le.1 hm

/-- **The rooted measure equals the DMS-shifted measure.** For a whole-plane GFF, `0 < γ < 2`, its `α = 0` LQG
measure `μ` and a measurable finite version `ρ` of `μ|_{B₁}`, `markedLeftMeas = markedRightMeas`. -/
theorem markedLeftMeas_eq_markedRightMeas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ρ : Ω → Measure ℂ} (hW : IsWholePlaneGFF P hC hcirc)
    (hL : IsLQGMeasureOfField P γ 0 hcirc μ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ : Measurable ρ)
    (hfin : ∀ ω, IsFiniteMeasure (ρ ω)) (hρμ : ∀ᵐ ω ∂P, (μ ω).restrict (ball (0 : ℂ) 1) = ρ ω) :
    markedLeftMeas P hC ρ = markedRightMeas P γ hC hcirc := by
  have hP : IsProbabilityMeasure P := hW.isGaussianProcess.isProbabilityMeasure
  have hfinR : IsFiniteMeasure (markedRightMeas P γ hC hcirc) := isFiniteMeasure_markedRightMeas hW
  have hLf : ∀ Ψ : MarkObs → ℝ≥0∞, Measurable Ψ → ∫⁻ x, Ψ x ∂(markedLeftMeas P hC ρ)
      = ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, z) ∂(μ ω) ∂P := by
    intro Ψ hΨ
    rw [markedLeftMeas, Measure.lintegral_bind (measurable_markedLeftKernel hW hρ hfin).aemeasurable
      hΨ.aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [hρμ] with ω hω
    have hm : Measurable fun z => obsM hC (ω, z) := (measurable_obsM hW).comp measurable_prodMk_left
    rw [markedLeftKernel, lintegral_map hΨ hm, ← hω]
    rfl
  have hRf : ∀ Ψ : MarkObs → ℝ≥0∞, Measurable Ψ → ∫⁻ x, Ψ x ∂(markedRightMeas P γ hC hcirc)
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P ∂volume := by
    intro Ψ hΨ
    rw [markedRightMeas, Measure.lintegral_bind
      (measurable_markedRightKernel (P := P) (γ := γ) hW).aemeasurable hΨ.aemeasurable]
    refine lintegral_congr fun z => ?_
    have hm : Measurable fun ω => obsMs γ hC hcirc (z, ω) := (measurable_obsMs γ hW).comp measurable_prodMk_left
    rw [markedRightKernel, lintegral_map hΨ hm]
    rfl
  have hcyl : ∀ s ∈ openCylinders, markedRightMeas P γ hC hcirc s = markedLeftMeas P hC ρ s := by
    rintro _ ⟨n, φ, A, V, hφ, hA, hV, rfl⟩
    let S : Set MarkObs := {x | (fun i => x.1 (φ i)) ∈ A ∧ x.2 ∈ V}
    let S' : Set MarkObs := S ∩ Prod.snd ⁻¹' ball (0 : ℂ) 1
    show markedRightMeas P γ hC hcirc S = markedLeftMeas P hC ρ S
    have hXm : Measurable fun x : MarkObs => fun i => x.1 (φ i) :=
      measurable_pi_iff.mpr fun i => measurable_eval_markObs (hφ i)
    have hS : MeasurableSet S := (hXm hA.measurableSet).inter (measurable_snd hV.measurableSet)
    have hS' : MeasurableSet S' := hS.inter (measurable_snd measurableSet_ball)
    have hind : ∀ (a : (ℂ → ℝ) → ℝ), ∀ z ∈ ball (0 : ℂ) 1,
        S.indicator (1 : MarkObs → ℝ≥0∞) (a, z) = S'.indicator 1 (a, z) := fun a z hz => by
      by_cases h : (a, z) ∈ S
      · rw [indicator_of_mem h, indicator_of_mem (show (a, z) ∈ S' from ⟨h, hz⟩)]
      · rw [indicator_of_notMem h, indicator_of_notMem fun h' => h h'.1]
    have hL1 : markedLeftMeas P hC ρ S = markedLeftMeas P hC ρ S' := by
      rw [← lintegral_indicator_one hS, ← lintegral_indicator_one hS', hLf _ (measurable_one.indicator hS),
        hLf _ (measurable_one.indicator hS')]
      exact lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_ball fun z hz => hind _ z hz
    have hR1 : markedRightMeas P γ hC hcirc S = markedRightMeas P γ hC hcirc S' := by
      rw [← lintegral_indicator_one hS, ← lintegral_indicator_one hS', hRf _ (measurable_one.indicator hS),
        hRf _ (measurable_one.indicator hS')]
      exact setLIntegral_congr_fun measurableSet_ball fun z hz => lintegral_congr fun ω => hind _ z hz
    -- continuous cutoffs of `A` and of `V ∩ B₁`
    obtain ⟨F, hFc, hF0, hF1, hFm, hFs, -⟩ := exists_cutoff_iSup_eq_indicator hA
    obtain ⟨G, hGc, hG0, hG1, hGm, hGs, hGt⟩ := exists_cutoff_iSup_eq_indicator (hV.inter (isOpen_ball (x := (0 : ℂ)) (ε := 1)))
    let Ψ : ℕ → MarkObs → ℝ≥0∞ := fun j x => ENNReal.ofReal (F j fun i => x.1 (φ i)) * ENNReal.ofReal (G j x.2)
    have hΨm : ∀ j, Measurable (Ψ j) := fun j =>
      ((hFc j).measurable.comp hXm).ennreal_ofReal.mul ((hGc j).measurable.comp measurable_snd).ennreal_ofReal
    have hΨmono : Monotone Ψ := fun i j hij x =>
      mul_le_mul' (ENNReal.ofReal_le_ofReal (hFm _ hij)) (ENNReal.ofReal_le_ofReal (hGm _ hij))
    have hΨsup : ∀ x, ⨆ j, Ψ j x = S'.indicator 1 x := fun x => by
      have ha : Tendsto (fun j => ENNReal.ofReal (F j fun i => x.1 (φ i))) atTop
          (𝓝 (A.indicator 1 fun i => x.1 (φ i))) := by
        rw [← hFs]
        exact tendsto_atTop_iSup fun i j hij => ENNReal.ofReal_le_ofReal (hFm _ hij)
      have hb : Tendsto (fun j => ENNReal.ofReal (G j x.2)) atTop
          (𝓝 ((V ∩ ball (0 : ℂ) 1).indicator 1 x.2)) := by
        rw [← hGs]
        exact tendsto_atTop_iSup fun i j hij => ENNReal.ofReal_le_ofReal (hGm _ hij)
      have hne : ∀ (Y : Type) (B : Set Y) (y : Y), B.indicator (1 : Y → ℝ≥0∞) y ≠ ∞ := fun Y B y => by
        by_cases h : y ∈ B <;> simp [h]
      have hab := ENNReal.Tendsto.mul ha (Or.inr (hne _ _ _)) hb (Or.inr (hne _ _ _))
      refine (tendsto_nhds_unique (tendsto_atTop_iSup fun i j hij => hΨmono hij x) hab).trans ?_
      by_cases h1 : (fun i => x.1 (φ i)) ∈ A <;> by_cases h2 : x.2 ∈ V <;>
        by_cases h3 : x.2 ∈ ball (0 : ℂ) 1 <;> simp [S', S, h1, h2, h3]
    have hΨeq : ∀ j, ∫⁻ x, Ψ j x ∂(markedLeftMeas P hC ρ) = ∫⁻ x, Ψ j x ∂(markedRightMeas P γ hC hcirc) := by
      intro j
      have hg1 : tsupport (G j) ⊆ ball (0 : ℂ) 1 := (hGt j).trans inter_subset_right
      have hgs : HasCompactSupport (G j) :=
        (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_tsupport _)
          (hg1.trans ball_subset_closedBall)
      have h6 := hW.lintegral_mul_lintegral_eq_dmsShifted hγ0 hγ2 hL hφ (hFc j) (hF0 j) (hF1 j) (hGc j) hgs hg1
        (hG0 j)
      have hsupp : Function.support (fun z => ENNReal.ofReal (G j z)) ⊆ ball (0 : ℂ) 1 :=
        Function.support_subset_iff'.2 fun z hz => by
          simp [image_eq_zero_of_notMem_tsupport fun h => hz (hg1 h)]
      rw [hLf _ (hΨm j), hRf _ (hΨm j)]
      calc _ = ∫⁻ ω, ENNReal.ofReal (F j fun i => hC ω (φ i)) * ∫⁻ z, ENNReal.ofReal (G j z) ∂(μ ω) ∂P := by
            refine lintegral_congr fun ω => ?_
            simp only [Ψ]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_eq_of_support_subset hsupp]
        _ = _ := h6
        _ = _ := by
            refine setLIntegral_congr_fun measurableSet_ball fun z _ => ?_
            simp only [Ψ]
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
            exact mul_comm _ _
    calc markedRightMeas P γ hC hcirc S = markedRightMeas P γ hC hcirc S' := hR1
      _ = ∫⁻ x, S'.indicator 1 x ∂(markedRightMeas P γ hC hcirc) := (lintegral_indicator_one hS').symm
      _ = ∫⁻ x, ⨆ j, Ψ j x ∂(markedRightMeas P γ hC hcirc) := lintegral_congr fun x => (hΨsup x).symm
      _ = ⨆ j, ∫⁻ x, Ψ j x ∂(markedRightMeas P γ hC hcirc) := lintegral_iSup hΨm hΨmono
      _ = ⨆ j, ∫⁻ x, Ψ j x ∂(markedLeftMeas P hC ρ) := iSup_congr fun j => (hΨeq j).symm
      _ = ∫⁻ x, ⨆ j, Ψ j x ∂(markedLeftMeas P hC ρ) := (lintegral_iSup hΨm hΨmono).symm
      _ = ∫⁻ x, S'.indicator 1 x ∂(markedLeftMeas P hC ρ) := lintegral_congr fun x => hΨsup x
      _ = markedLeftMeas P hC ρ S' := lintegral_indicator_one hS'
      _ = markedLeftMeas P hC ρ S := hL1.symm
  have huniv : (univ : Set MarkObs) ∈ openCylinders :=
    ⟨0, Fin.elim0, univ, univ, fun i => i.elim0, isOpen_univ, isOpen_univ, by ext x; simp⟩
  exact (ext_of_generate_finite openCylinders generateFrom_openCylinders.symm isPiSystem_openCylinders hcyl
    (hcyl univ huniv)).symm

end CampbellKernel

/-- **Duplantier-Miller-Sheffield, Lemma A.10, whole-plane clause for `D = B₁`, marked and unnormalized.** For a
whole-plane GFF, `0 < γ < 2` and its `α = 0` LQG measure `μ`, for every measurable test `Ψ` on pairing × mark,
`E ∫_{B₁} Ψ(h, z) dμ(z) = ∫_{B₁} E Ψ(h + f_z + κ, z) dz`. -/
theorem dmsLemmaA10WholePlaneMarkedSub_holds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) :
    DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ := by
  intro hW hL hγ0 hγ2 Ψ hΨ
  have hP : IsProbabilityMeasure P := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨ρ, hρ, hfin, hρμ⟩ := CampbellKernel.exists_measurable_finite_restrict hW hL
  exact CampbellKernel.lintegral_marked_eq_of_measures_eq hW hρ hfin hρμ
    (CampbellKernel.markedLeftMeas_eq_markedRightMeas hW hL hγ0 hγ2 hρ hfin hρμ) Ψ hΨ

end HarmonicBalls
