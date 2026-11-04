import HarmonicBalls.Proofs.Sec6.GreenUniformBound
import HarmonicBalls.Proofs.Sec6.BrownianHittingTransfer
import HarmonicBalls.Proofs.Sec5.GeneralDomainInteriorGreen

/-! # Stopped Green potentials in bounded domains

The harmonicity of the greatest harmonic minorant gives off-pole harmonicity
in its evaluation variable. Symmetry transfers this to the pole variable.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Metric InnerProductSpace ProbabilityTheory MarkovProcess Filter
open scoped NNReal ENNReal ContDiff ZeroAtInfty Topology

/-- For a bounded open domain, the Green kernel is harmonic in its second
variable away from its pole. -/
theorem harmonicOnNhd_greenFunction_right {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {x : ℂ} (hx : x ∈ U) :
    HarmonicOnNhd (greenFunction U x) (U \ {x}) := by
  have hh := harmonicOnNhd_greatestHarmonicMinorant_newtonKernel hU hUb hx
  intro z hz
  have hopen : IsOpen (U \ {x}) := hU.sdiff isClosed_singleton
  have heq : greenFunction U x =ᶠ[𝓝 z]
      fun w => newtonKernel x w - (greatestHarmonicMinorant U (newtonKernelEReal x) w).toReal := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    rw [greenFunction, ite_eq_left ⟨hx, hw.1, Ne.symm hw.2⟩]
  exact (harmonicAt_congr_nhds heq).2 ((harmonicAt_newtonKernel hz.2).sub (hh z hz.1))

/-- Green symmetry and off-pole harmonicity imply joint Borel measurability
of the Green kernel, including its prescribed diagonal and exterior values. -/
theorem measurable_greenFunction_uncurry_of_symmetry {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U)
    (hsymm : ∀ x y, greenFunction U x y = greenFunction U y x) :
    Measurable (fun p : ℂ × ℂ => greenFunction U p.2 p.1) := by
  classical
  let a : StronglyMeasurable (id : ℂ → ℂ) := stronglyMeasurable_id
  let t : ℕ → SimpleFunc ℂ ℂ := a.approx
  let good : Set (ℂ × ℂ) := {p | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2}
  have hgood : MeasurableSet good :=
    (hU.measurableSet.preimage measurable_fst).inter
      ((hU.measurableSet.preimage measurable_snd).inter isClosed_diagonal.measurableSet.compl)
  have happrox (n : ℕ) : Measurable (fun p : ℂ × ℂ => greenFunction U (t n p.1) p.2) := by
    have hcount : Measurable (fun p : (t n).range × ℂ => greenFunction U p.1 p.2) :=
      measurable_from_prod_countable_right (fun j => measurable_greenFunction hU j)
    have hf : Measurable (fun p : ℂ × ℂ =>
        (⟨t n p.1, SimpleFunc.mem_range_self (t n) p.1⟩ : (t n).range)) :=
      ((t n).measurable.comp measurable_fst).subtype_mk
    exact hcount.comp (hf.prodMk measurable_snd)
  have hlim : Tendsto (fun n : ℕ => good.indicator
      (fun p : ℂ × ℂ => greenFunction U (t n p.1) p.2)) atTop
      (𝓝 (good.indicator (fun p : ℂ × ℂ => greenFunction U p.2 p.1))) := by
    rw [tendsto_pi_nhds]
    intro p
    by_cases hp : p ∈ good
    · simp only [indicator_of_mem hp]
      have hc := (harmonicOnNhd_greenFunction_right hU hUb hp.2.1 p.1
        ⟨hp.1, hp.2.2⟩).1.continuousAt
      have h := hc.tendsto.comp (a.tendsto_approx p.1)
      change Tendsto (fun n : ℕ => greenFunction U (t n p.1) p.2) atTop
        (𝓝 (greenFunction U p.2 p.1))
      convert h using 1
      funext n
      exact hsymm _ _
    · simpa only [indicator_of_notMem hp] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hm := measurable_of_tendsto_metrizable (fun n => (happrox n).indicator hgood) hlim
  convert hm using 1
  funext p
  by_cases hp : p ∈ good
  · simp only [indicator_of_mem hp]
  · rw [indicator_of_notMem hp]
    by_cases hx : p.1 ∈ U
    · by_cases hy : p.2 ∈ U
      · have hxy : p.1 = p.2 := by
          by_contra hne
          exact hp ⟨hx, hy, hne⟩
        rw [hxy, greenFunction_self]
      · exact greenFunction_of_notMem_left hy p.1
    · exact greenFunction_of_notMem_right hx p.2

/-- Green symmetry makes a restricted Green potential harmonic off its compact
support, under Hölder regularity. -/
theorem harmonicOnNhd_restricted_greenPotential_of_symmetry
    {U L : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : IsCompact L) (hLU : L ⊆ U) {μ : Measure ℂ} (hfinite : μ L < ⊤)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    (hsymm : ∀ x y, greenFunction U x y = greenFunction U y x) :
    HarmonicOnNhd (fun z => ∫ x in L, greenFunction U z x ∂μ) (U \ L) := by
  apply harmonicOnNhd_restricted_greenPotential_of_kernel_and_holder_of_bounded
    hU hUb hL hLU hfinite hholder ?_ (measurable_greenFunction_uncurry_of_symmetry hU hUb hsymm)
  intro x hx
  have hh := (harmonicOnNhd_greenFunction_right hU hUb (hLU hx)).mono
    (show U \ L ⊆ U \ {x} from fun z hz => ⟨hz.1, fun hzx => hz.2 (hzx ▸ hx)⟩)
  simpa only [hsymm] using hh

/-- A stopped Green-potential bound in a bounded open domain, with symmetry
and the planar generator identification explicit. -/
theorem restricted_greenPotential_stopped_representation_of_symmetry
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {U L : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hL : IsCompact L) (hLU : L ⊆ U)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    (hsymm : ∀ x y, greenFunction U x y = greenFunction U y x)
    {x : ℂ} (hx : x ∈ U \ L)
    (hgen : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ z, (f : C₀(ℂ, ℝ)) z = g z) ∧
        ∀ z, HarmonicAt g z →
          (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0) :
    ENNReal.ofReal (∫ y in L, greenFunction U x y ∂μ) ≤ ∫⁻ path,
      ENNReal.ofReal (∫ y in L,
        greenFunction U (path ((ContinuousPath.exitTime (U \ L) path).toNNReal)) y ∂μ)
          ∂(planarBrownianMotion x) := by
  exact restricted_greenPotential_stopped_representation_of_harmonic hU hUb hL hLU hholder hx
    (harmonicOnNhd_restricted_greenPotential_of_symmetry hU hUb hL hLU hL.measure_lt_top
      hholder hsymm) hgen

universe u

/-- The fine-support hitting estimate follows from the LQG regularity inputs,
annular Green symmetry and planar generator identification. -/
theorem ae_lqg_fineSupport_hitting_bound_of_symmetry
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hsymm : ∀ c : ℂ, ∀ r : ℝ, 0 < r → ∀ x y,
      greenFunction (fineSupportAnnulus c r) x y = greenFunction (fineSupportAnnulus c r) y x)
    (hgen : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ z, (f : C₀(ℂ, ℝ)) z = g z) ∧
        ∀ z, HarmonicAt g z →
          (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0) :
    ∀ᵐ sample ∂P, ∀ x : ℂ, ∀ ε : ℝ, 0 < ε →
      ∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Monotone K →
      (μ sample) (ball x ε \ ⋃ n, K n) = 0 →
      ∀ᶠ n in atTop,
        ENNReal.ofReal (greenPotentialExtremaRatio (fineSupportAnnulus x (fineSupportScale n))
          (sphere x (fineSupportScale n / 4)) (μ sample)) ≤ planarBrownianMotion x
        {path | ContinuousPath.exitTime (⋃ n, K n)ᶜ path ≤
          ContinuousPath.exitTime (ball x (fineSupportScale n)) path} := by
  apply ae_lqg_fineSupport_hitting_bound_of_stopped_representation
    hholder hfull hgrowth hγ hγ2 hα hGFF hμ hnonatom
  filter_upwards [hholder γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hμ] with sample hhold hsample
  let : IsLocallyFiniteMeasure (μ sample) := hsample.isLocallyFiniteMeasure
  intro c r hr L hL hLU x hx hxL
  obtain ⟨hO, _, _, hSO, _⟩ := fineSupportAnnulus_geometry c hr
  have hopen : IsOpen (fineSupportAnnulus c r) := by
    obtain ⟨ρ, hρ, hEq, _⟩ := hO.2
    rw [hEq]
    exact isOpen_lt hρ.continuous continuous_const
  exact restricted_greenPotential_stopped_representation_of_symmetry hopen hO.1 hL hLU
    (hhold _ hO) (hsymm c r hr) ⟨hSO hx, hxL⟩ hgen

end HarmonicBalls.Section6
