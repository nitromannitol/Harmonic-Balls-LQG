import HarmonicBalls.Proofs.Sec6.GreenPotentialCompactApproximation
import HarmonicBalls.Proofs.Sec6.BrownianBallCrossing
import HarmonicBalls.Proofs.Sec6.RecurrenceFubini
import HarmonicBalls.Proofs.Sec6.AnnulusGeometry

/-!
# Green-potential hitting bounds and compact approximation

The compact Green-potential hitting estimate passes to a full-measure increasing
union. The compact-set hitting estimate remains an explicit hypothesis.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology

/-- If compact subsets obey the Green-potential hitting estimate, then so does a
full-measure increasing union, with the full potential in the numerator. -/
theorem greenPotential_hitting_union_of_compact_hitting
    {μ : Measure ℂ} {O S : Set ℂ} {K : ℕ → Set ℂ} {M : ℝ}
    (hopen : IsOpen O) (hbounded : Bornology.IsBounded O)
    (hS : IsCompact S) (hSO : S ⊆ closure O)
    (hK : ∀ n, IsCompact (K n)) (hKmono : Monotone K)
    (hfull : μ (O \ ⋃ n, K n) = 0)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure O)) →
      (∀ x ∈ closure O, IntegrableOn (fun y => greenFunction O x y * f y) O μ) ∧
      ∃ C r : ℝ≥0, 0 < r ∧
        HolderOnWith C r (fun x => ∫ y in O, greenFunction O x y * f y ∂μ) (closure O))
    (hcompact : ∀ L : Set ℂ, IsCompact L → L ⊆ O → ∀ z ∈ S,
      ENNReal.ofReal ((∫ y in L, greenFunction O z y ∂μ) / M) ≤
        planarBrownianMotion z
          {ω | ContinuousPath.exitTime Lᶜ ω ≤ ContinuousPath.exitTime O ω}) :
    ∀ z ∈ S, ENNReal.ofReal (greenPotential O μ z / M) ≤
      planarBrownianMotion z
        {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤ ContinuousPath.exitTime O ω} := by
  obtain ⟨L, hLc, hLm, hLsub, hLu, hconv⟩ :=
    exists_compact_greenPotential_approximation hopen hbounded hS hSO hK hKmono hfull hholder
  intro z hz
  have hlim : Tendsto (fun n => ENNReal.ofReal
      ((∫ y in L n, greenFunction O z y ∂μ) / M)) atTop
      (𝓝 (ENNReal.ofReal (greenPotential O μ z / M))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((hconv.tendsto_at hz).div_const M)
  apply le_of_tendsto hlim
  filter_upwards [] with n
  refine (hcompact (L n) (hLc n) ((hLsub n).trans inter_subset_right) z hz).trans ?_
  apply measure_mono
  intro ω hω
  have hsubset : L n ⊆ ⋃ i, K i := (hLsub n).trans
    (inter_subset_left.trans (subset_iUnion K n))
  exact (ContinuousPath.exitTime_mono (compl_subset_compl.mpr hsubset) ω).trans hω


/-- The extrema ratio is bounded by the potential at any point of the test set,
normalized by the real value of the domain supremum. -/
theorem greenPotentialExtremaRatio_le_potential_div_sup
    {μ : Measure ℂ} {O S : Set ℂ} (hO : Bornology.IsBounded O) {z : ℂ} (hz : z ∈ S) :
    ENNReal.ofReal (greenPotentialExtremaRatio O S μ) ≤
      ENNReal.ofReal (greenPotential O μ z /
        (⨆ y : O, ENNReal.ofReal (greenPotential O μ y)).toReal) := by
  have hmin : (⨅ y : S, ENNReal.ofReal (greenPotential O μ y)).toReal ≤
      greenPotential O μ z := by
    calc
      _ ≤ (ENNReal.ofReal (greenPotential O μ z)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (iInf_le _ (⟨z, hz⟩ : S))
      _ = greenPotential O μ z := ENNReal.toReal_ofReal (greenPotential_nonneg hO μ z)
  unfold greenPotentialExtremaRatio
  rw [ENNReal.toReal_div]
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right hmin ENNReal.toReal_nonneg


/-- The compact-set hitting estimate implies the full extrema-ratio bound for
all starting points in the compact test set. -/
theorem greenPotentialExtremaRatio_hitting_union_of_compact_hitting
    {μ : Measure ℂ} {O S : Set ℂ} {K : ℕ → Set ℂ}
    (hopen : IsOpen O) (hbounded : Bornology.IsBounded O)
    (hS : IsCompact S) (hSO : S ⊆ closure O)
    (hK : ∀ n, IsCompact (K n)) (hKmono : Monotone K)
    (hfull : μ (O \ ⋃ n, K n) = 0)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure O)) →
      (∀ x ∈ closure O, IntegrableOn (fun y => greenFunction O x y * f y) O μ) ∧
      ∃ C r : ℝ≥0, 0 < r ∧
        HolderOnWith C r (fun x => ∫ y in O, greenFunction O x y * f y ∂μ) (closure O))
    (hcompact : ∀ L : Set ℂ, IsCompact L → L ⊆ O → ∀ z ∈ S,
      ENNReal.ofReal ((∫ y in L, greenFunction O z y ∂μ) /
        (⨆ y : O, ENNReal.ofReal (greenPotential O μ y)).toReal) ≤
        planarBrownianMotion z
          {ω | ContinuousPath.exitTime Lᶜ ω ≤ ContinuousPath.exitTime O ω}) :
    ∀ z ∈ S, ENNReal.ofReal (greenPotentialExtremaRatio O S μ) ≤
      planarBrownianMotion z
        {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤ ContinuousPath.exitTime O ω} := by
  intro z hz
  exact (greenPotentialExtremaRatio_le_potential_div_sup hbounded hz).trans
    (greenPotential_hitting_union_of_compact_hitting hopen hbounded hS hSO hK hKmono
      hfull hholder hcompact z hz)


/-- For a fine-support annulus, local full mass and the compact-set hitting
estimate give the extrema-ratio bound from every point of the interior circle. -/
theorem fineSupport_circle_hitting_union_of_compact_hitting
    {μ : Measure ℂ} {c : ℂ} {r ε : ℝ} (hr : 0 < r) (hrε : r ≤ ε)
    {K : ℕ → Set ℂ} (hK : ∀ n, IsCompact (K n)) (hKmono : Monotone K)
    (hfull : μ (ball c ε \ ⋃ n, K n) = 0)
    (hholder : ∀ O : Set ℂ, IsSmoothBoundedOpen O → ∀ f : ℂ → ℝ,
      MemLp f ⊤ (μ.restrict (closure O)) →
      (∀ x ∈ closure O, IntegrableOn (fun y => greenFunction O x y * f y) O μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in O, greenFunction O x y * f y ∂μ) (closure O))
    (hcompact : ∀ L : Set ℂ, IsCompact L → L ⊆ fineSupportAnnulus c r →
      ∀ z ∈ sphere c (r / 4),
      ENNReal.ofReal ((∫ y in L, greenFunction (fineSupportAnnulus c r) z y ∂μ) /
        (⨆ y : fineSupportAnnulus c r,
          ENNReal.ofReal (greenPotential (fineSupportAnnulus c r) μ y)).toReal) ≤
        planarBrownianMotion z {ω | ContinuousPath.exitTime Lᶜ ω ≤
          ContinuousPath.exitTime (fineSupportAnnulus c r) ω}) :
    ∀ z ∈ sphere c (r / 4),
      ENNReal.ofReal (greenPotentialExtremaRatio (fineSupportAnnulus c r)
        (sphere c (r / 4)) μ) ≤
      planarBrownianMotion z {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
        ContinuousPath.exitTime (fineSupportAnnulus c r) ω} := by
  obtain ⟨hO, hS, _, hSO, _⟩ := fineSupportAnnulus_geometry c hr
  have hopen : IsOpen (fineSupportAnnulus c r) := by
    obtain ⟨ρ, hρ, hEq, _⟩ := hO.2
    rw [hEq]
    exact isOpen_lt hρ.continuous continuous_const
  have hsub : fineSupportAnnulus c r ⊆ ball c ε := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hz.2 hrε
  apply greenPotentialExtremaRatio_hitting_union_of_compact_hitting
    hopen hO.1 hS (hSO.trans subset_closure) hK hKmono ?_ (hholder _ hO) hcompact
  exact measure_mono_null (sdiff_subset_sdiff_left hsub) hfull


/-- Hitting before leaving the fine-support annulus entails hitting before
leaving its outer ball. -/
theorem fineSupport_hitting_annulus_le_hitting_ball
    (c z : ℂ) (r : ℝ) (E : Set ℂ) :
    planarBrownianMotion z {ω | ContinuousPath.exitTime Eᶜ ω ≤
      ContinuousPath.exitTime (fineSupportAnnulus c r) ω} ≤
    planarBrownianMotion z {ω | ContinuousPath.exitTime Eᶜ ω ≤
      ContinuousPath.exitTime (ball c r) ω} := by
  apply measure_mono
  intro ω hω
  change ContinuousPath.exitTime Eᶜ ω ≤ ContinuousPath.exitTime (ball c r) ω
  apply hω.trans
  apply ContinuousPath.exitTime_mono
  intro y hy
  simpa only [mem_ball, dist_eq_norm] using hy.2

end HarmonicBalls.Section6
