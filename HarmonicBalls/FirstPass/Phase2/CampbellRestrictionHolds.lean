import HarmonicBalls.FirstPass.Phase2.CampbellShiftCM
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.FirstPass.S11r.RootedJoint
import HarmonicBalls.FirstPass.S11w.MarkedKernel
import HarmonicBalls.Proofs.GFF.BackgroundChargeParameter

/-!
# The local Campbell marked restriction, derived

`LocalCampbellMarkedRestrictionFrozen` (Frozen/S11c.lean) as a theorem. Let `U = B(c₁, r₁)` with
`closedBall c₁ r₁ ⊆ D = B(c₂, r₂)` and `0 ∉ closedBall c₂ r₂`, and let `S` be a measurable set of marked restrictions
`(z, h|_D mod ℝ)` that is null for the Lebesgue mixture over `z ∈ U` of the laws of the Campbell reference observation
(`g - γ log|· - z| + b` restricted to `D`). Then `1_S(z, h|_D) = 0` for `μ_h`-almost every `z ∈ U`, almost surely, so
the Campbell law `P(dh) 1_U(z) μ_h(dz) / μ_h(U)` gives `S` mass zero.

Proof (Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Lemma A.10, applied on translated unit discs):
1. the reference null hypothesis gives `P(ref_z ∈ S) = 0` for Lebesgue-a.e. `z ∈ U`, hence (Cameron-Martin step,
   `CampbellShiftCM.lintegral_dmsShifted_eq_zero`) the observation of the Lemma A.10 output on `B_1(a)` is null too;
2. the rooted identity on `B_1(a)` (`CampbellObsTransfer.lintegral_translate_campbell`) for the `α = 0` LQG measure `μ₀`
   (`lqgMeasureExistence_derived`) gives `E[e^{-γ h_1(a)} ∫_{B_1(a) ∩ U} 1_S dμ₀] = 0`, so the inner integral vanishes
   almost surely (`aemeasurable_setLIntegral_lqg` supplies the measurability);
3. countably many unit discs cover the plane, and on `U` (open, bounded, away from `0`) the measure `μ` is
   `|z|^{-γα₀} μ₀` (`IsLQGLimit.restrict_fieldCircleAverage_eq`), absolutely continuous with respect to `μ₀`.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

namespace HarmonicBalls

namespace CampbellRestrictionHolds

open CampbellObsTransfer

/-- **Measurability of set integrals against the LQG measure.** For the γ-LQG measure `μ` of `h^ℂ - α₀ log|·|`
(`α₀ < Q`), a bounded Borel set `B` and a jointly measurable integrand `g`, the map `ω ↦ ∫_B g(ω, z) dμ_ω(z)` is almost
surely measurable: `μ` agrees almost surely with a jointly measurable version, whose restriction to a closed disc
containing `B` is a measurable family of finite measures on the event (measurable, of full measure) where that disc has
finite mass. -/
theorem aemeasurable_setLIntegral_lqg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ α₀ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {B : Set ℂ} (hB : MeasurableSet B) (hBb : Bornology.IsBounded B) {g : Ω × ℂ → ℝ≥0∞} (hg : Measurable g) :
    AEMeasurable (fun ω => ∫⁻ z in B, g (ω, z) ∂(μ ω)) P := by
  obtain ⟨M, hM, hMlim⟩ := Section6.exists_jointly_measurable_subcritical_lqgMeasures P γ hγ hγ2 hC hcirc hG
    (fun n => lqgMeasureExistence_derived P γ _ hC hcirc)
  have hν : Measurable fun ω => M (ω, α₀) := hM.comp (measurable_id.prodMk measurable_const)
  have hae : ∀ᵐ ω ∂P, μ ω = M (ω, α₀) := S11c.ae_eq_joint_version hMlim hμ hα₀
  have hfinite := S11w.ae_forall_measure_closedBall_ne_top hμ
  obtain ⟨R, hR⟩ := hBb.subset_closedBall (0 : ℂ)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, R ≤ N := exists_nat_ge R
  have hBN : B ⊆ closedBall (0 : ℂ) (N : ℝ) := hR.trans (closedBall_subset_closedBall hN)
  have hGm : MeasurableSet {ω : Ω | M (ω, α₀) (closedBall (0 : ℂ) (N : ℝ)) ≠ ∞} :=
    ((Measure.measurable_measure.1 hν _ measurableSet_closedBall) (measurableSet_singleton ∞)).compl
  set κ : Ω → Measure ℂ := fun ω => if M (ω, α₀) (closedBall (0 : ℂ) (N : ℝ)) ≠ ∞ then
    (M (ω, α₀)).restrict (closedBall (0 : ℂ) (N : ℝ)) else 0 with hκdef
  have hκ : Measurable κ := by
    refine Measurable.ite hGm ?_ measurable_const
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    simp only [Measure.restrict_apply hs]
    exact Measure.measurable_measure.1 hν _ (hs.inter measurableSet_closedBall)
  have hκfin : ∀ ω, IsFiniteMeasure (κ ω) := by
    intro ω
    by_cases hω : M (ω, α₀) (closedBall (0 : ℂ) (N : ℝ)) = ∞
    · simp only [hκdef, hω, ne_eq, not_true_eq_false, ↓reduceIte]
      infer_instance
    · simp only [hκdef, hω, ne_eq, not_false_eq_true, ↓reduceIte]
      exact ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hω⟩
  have hgB : Measurable fun p : Ω × ℂ => (Prod.snd ⁻¹' B).indicator g p :=
    hg.indicator (measurable_snd hB)
  refine (S11w.measurable_lintegral_of_finite_family hκ hκfin hgB).aemeasurable.congr ?_
  filter_upwards [hae, hfinite] with ω hω hωf
  have hfin : ¬ M (ω, α₀) (closedBall (0 : ℂ) (N : ℝ)) = ∞ := by rw [← hω]; exact hωf N
  simp only [hκdef, hfin, ne_eq, not_false_eq_true, ↓reduceIte]
  rw [← hω]
  have hpt : ∀ z, (Prod.snd ⁻¹' B).indicator g (ω, z) = B.indicator (fun z => g (ω, z)) z := fun z => rfl
  rw [lintegral_congr hpt, lintegral_indicator hB, Measure.restrict_restrict hB, inter_eq_left.2 hBN]

end CampbellRestrictionHolds

open CampbellObsTransfer CampbellRestrictionHolds

/-- **The local Campbell marked restriction (Duplantier-Miller-Sheffield, Lemma A.10, local form), derived.**
`LocalCampbellMarkedRestrictionFrozen` holds: for discs `U = B(c₁, r₁)`, `closedBall c₁ r₁ ⊆ D = B(c₂, r₂)`,
`0 ∉ closedBall c₂ r₂`, every measurable set of marked restrictions `(z, h|_D mod ℝ)` that is null for the Lebesgue
mixture over `z ∈ U` of the laws of the reference observation `(g - γ log|· - z| + b)|_D` is null for the Campbell law
`P(dh) 1_U(z) μ_h(dz) / μ_h(U)`. -/
theorem localCampbellMarkedRestriction_holds : LocalCampbellMarkedRestrictionFrozen.{u} := by
  intro γ α₀ hγ hγ2 hα₀ Ω _ P _ hC hcirc μ hh hμ c₁ c₂ r₁ r₂ hr₁ hr₂ hsub h0 S hS href
  set U : Set ℂ := ball c₁ r₁ with hUdef
  have hUo : IsOpen U := isOpen_ball
  have hUm : MeasurableSet U := measurableSet_ball
  have hUb : Bornology.IsBounded U := isBounded_ball
  have hDb : Bornology.IsBounded (ball c₂ r₂) := isBounded_ball
  have h0U : (0 : ℂ) ∉ U := fun h => h0 (ball_subset_closedBall (hsub (ball_subset_closedBall h)))
  obtain ⟨μ₀, hμ₀⟩ := lqgMeasureExistence_derived P γ 0 hC hcirc hh hγ hγ2 (lqgQ_pos hγ)
  -- the marked observation is jointly measurable
  have hobs : Measurable fun p : Ω × ℂ => campbellMarkedObs α₀ (ball c₂ r₂) (hC p.1) p.2 := by
    unfold campbellMarkedObs
    refine Measurable.prodMk measurable_snd ?_
    refine Measurable.of_eval (fun φ => ?_)
    have hφ : IsTestFunction Set.univ φ.1 := ⟨φ.2.1.1, φ.2.1.2.1, Set.subset_univ _⟩
    unfold fieldPairing
    exact ((hh.measurable_pairing φ.1 hφ).comp measurable_fst).sub measurable_const
  set S' : Set (ℂ × (MeanZeroTest (ball c₂ r₂) → ℝ)) := S ∩ (U ×ˢ univ) with hS'def
  have hS' : MeasurableSet S' := hS.inter (hUm.prod MeasurableSet.univ)
  set g : Ω × ℂ → ℝ≥0∞ := fun p =>
    S'.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC p.1) p.2) with hgdef
  have hg : Measurable g := (measurable_const.indicator hS').comp hobs
  -- step 1: the reference observation is null for Lebesgue-a.e. root in `U`
  have hFm : Measurable fun z =>
      ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P :=
    ((measurable_const.indicator hS).comp
      (measurable_campbellReferenceObs_joint P hC hcirc hh γ α₀ (ball c₂ r₂))).lintegral_prod_right'
  have hnull : ∀ᵐ z ∂volume, z ∈ U →
      ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P = 0 := by
    have h1 := (lintegral_eq_zero_iff hFm).1 href
    have h2 : ∀ᵐ z ∂(volume.restrict U),
        ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P = 0 := h1
    exact (ae_restrict_iff' hUm).1 h2
  -- step 2: the right side of the rooted identity on `B_1(a)` vanishes for `S ∩ (U × univ)`
  have hRHS : ∀ a : ℂ, ∫⁻ z in ball a 1, ∫⁻ ω, S'.indicator (fun _ => (1 : ℝ≥0∞))
      (z, fun φ : MeanZeroTest (ball c₂ r₂) => fieldPairing α₀ (hC ω) φ.1 + ∫ y, dmsShift γ (z - a) (y - a) * φ.1 y)
      ∂P ∂volume = 0 := by
    intro a
    refine (lintegral_congr_ae (ae_restrict_of_ae ?_)).trans lintegral_zero
    filter_upwards [hnull] with z hz
    by_cases hzU : z ∈ U
    · refine le_antisymm ?_ zero_le
      calc _ ≤ ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
              (z, fun φ : MeanZeroTest (ball c₂ r₂) => fieldPairing α₀ (hC ω) φ.1
                + ∫ y, dmsShift γ (z - a) (y - a) * φ.1 y) ∂P :=
            lintegral_mono fun ω => indicator_le_indicator_of_subset inter_subset_left
              (fun _ => zero_le) _
        _ = 0 := CampbellShiftCM.lintegral_dmsShifted_eq_zero hh γ α₀ hDb a z hS (hz hzU)
    · exact (lintegral_congr fun ω => indicator_of_notMem (fun h => hzU (mem_prod.1 h.2).1) _).trans
        lintegral_zero
  -- step 3: on each unit disc, `∫_{B_1(a)} 1_{S ∩ (U × univ)} dμ₀ = 0` almost surely
  have hX : ∀ a : ℂ, ∀ᵐ ω ∂P, ∫⁻ z in ball a 1, g (ω, z) ∂(μ₀ ω) = 0 := by
    intro a
    have hT := lintegral_translate_campbell hγ hγ2 hh hμ₀ α₀ (ball c₂ r₂) a hS'
    rw [hRHS a] at hT
    have hc : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (-(γ * hcirc ω 1 a)))) P :=
      (((hh.measurable_circle 1 a one_pos).const_mul γ).neg.exp.ennreal_ofReal).aemeasurable
    have hXm := aemeasurable_setLIntegral_lqg P hγ hγ2 (lqgQ_pos hγ) hh hμ₀ (measurableSet_ball (x := a) (ε := 1))
      isBounded_ball hg
    have h0' := (lintegral_eq_zero_iff' (hc.mul hXm)).1 hT
    filter_upwards [h0'] with ω hω
    have hω' : ENNReal.ofReal (Real.exp (-(γ * hcirc ω 1 a))) * ∫⁻ z in ball a 1, g (ω, z) ∂(μ₀ ω) = 0 := hω
    exact (mul_eq_zero.1 hω').resolve_left (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  -- step 4: countably many unit discs cover the plane; transfer to `μ` on `U`
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ℂ
  have hcover : (⋃ n, ball (u n) 1) = univ := eq_univ_of_forall fun z => by
    obtain ⟨n, hn⟩ := hu.exists_dist_lt z one_pos
    exact mem_iUnion.2 ⟨n, mem_ball.2 hn⟩
  have hall : ∀ᵐ ω ∂P, ∀ n, ∫⁻ z in ball (u n) 1, g (ω, z) ∂(μ₀ ω) = 0 := ae_all_iff.2 fun n => hX (u n)
  have hμ₀' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ₀ ω) := hμ₀
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  have hA : ∀ᵐ ω ∂P, ∫⁻ z in U, S.indicator (fun _ => (1 : ℝ≥0∞))
      (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 := by
    filter_upwards [hall, hμ₀', hμ', hh.ae_continuousOn_circle] with ω hω hL0 hL hc
    have hg0 : ∀ᵐ z ∂(μ₀ ω), g (ω, z) = 0 := by
      have hn : ∀ n, ∀ᵐ z ∂(μ₀ ω).restrict (ball (u n) 1), g (ω, z) = 0 := fun n =>
        (lintegral_eq_zero_iff (hg.comp measurable_prodMk_left)).1 (hω n)
      have h' := (ae_restrict_iUnion_iff (fun n => ball (u n) 1) (fun z => g (ω, z) = 0)).2 hn
      rwa [hcover, Measure.restrict_univ] at h'
    have hm : ∀ k : ℕ, Measurable (hcirc ω (dyadicScale k)) := fun k =>
      (hc.comp_continuous (continuous_const.prodMk continuous_id)
        fun z => mk_mem_prod (mem_Ioi.2 (dyadicScale_pos k)) (mem_univ z)).measurable
    rw [fieldCircleAverage_zero_eq] at hL0
    have hres := IsLQGLimit.restrict_fieldCircleAverage_eq hm hL0 hL hUo hUb h0U
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    rw [hres]
    refine (ae_restrict_iff' hUm).2 ?_
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le hg0] with z hz hzU
    have hz' : S'.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) = 0 := hz
    have hmem : ∀ x : MeanZeroTest (ball c₂ r₂) → ℝ, (z, x) ∈ U ×ˢ (univ : Set (MeanZeroTest (ball c₂ r₂) → ℝ)) :=
      fun x => mk_mem_prod hzU (mem_univ x)
    have himp := indicator_apply_eq_zero.1 hz'
    exact indicator_apply_eq_zero.2 fun hzS => himp (mem_inter hzS (hmem _))
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hA] with ω hω
  rw [hω, mul_zero]

end HarmonicBalls
