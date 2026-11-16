import HarmonicBalls.Proofs.Potential.LQGClockAnnularUniformIntegrability
import HarmonicBalls.Proofs.Potential.LQGClockAnnularUniformIncrement

/-! # Annular clock increments under the product law

The product-law expectation of an annular increment agrees with its iterated
field and Brownian expectation.
-/

open MeasureTheory MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The joint nonnegative integral of the annular increment is the annealed
expectation of its field-averaged absolute value. -/
theorem lintegral_prod_annularIncrementSample_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    (∫⁻ p : Ω × ContinuousPath ℂ,
      ENNReal.ofReal |annularIncrementSample hcirc γ α δ ε τ p.2 p.1|
      ∂(P.prod (planarBrownianMotion x))) =
      ENNReal.ofReal (∫ b, stoppedAnnularIncrement P hcirc γ α δ ε τ b
        ∂(planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨F, hFm, _, hFae⟩ :=
    exists_integrable_annularIncrementSample hh hγ0 hγ2 α x hε hεhalf hεδ τ hτ
  have heq : (fun p : Ω × ContinuousPath ℂ =>
      ENNReal.ofReal |annularIncrementSample hcirc γ α δ ε τ p.2 p.1|) =ᵐ[
        P.prod (planarBrownianMotion x)]
      (fun p => ENNReal.ofReal |F (p.2,p.1)|) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae hFae] with p hp
    rw [hp p.2]
  rw [lintegral_congr_ae heq]
  have hmeas : Measurable (fun p : Ω × ContinuousPath ℂ => ENNReal.ofReal |F (p.2,p.1)|) :=
    ENNReal.measurable_ofReal.comp ((hFm.comp measurable_swap).abs)
  rw [lintegral_prod_symm _ hmeas.aemeasurable]
  have hfield (b : ContinuousPath ℂ) : Integrable (fun ω => F (b, ω)) P := by
    apply (integrable_stopped_annular_increment_field hh hε hεhalf hεδ γ α τ b).congr
    filter_upwards [hFae] with ω hω
    exact (hω b).symm
  have hinner (b : ContinuousPath ℂ) :
      (∫⁻ ω, ENNReal.ofReal |F (b,ω)| ∂P) =
        ENNReal.ofReal (stoppedAnnularIncrement P hcirc γ α δ ε τ b) := by
    simp_rw [← Real.norm_eq_abs]
    rw [← ofReal_integral_eq_lintegral_ofReal (hfield b).norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))]
    congr 1
    unfold stoppedAnnularIncrement
    apply integral_congr_ae
    filter_upwards [hFae] with ω hω
    rw [hω b]
    rfl
  simp_rw [hinner]
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_stopped_annular_inserted_increment_annealed_le hh hγ0 hγ2 α x
      (hε.trans_le hεδ) τ hτ
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · exact (hb ε hε hεhalf hεδ).1
  · exact Filter.Eventually.of_forall (fun b => integral_nonneg (fun ω => abs_nonneg _))

/-- The annealed increment bound has constants independent of the measurable horizon. -/
theorem brownian_stopped_annular_inserted_increment_annealed_le_uniform_horizon
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    : ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (τ : ContinuousPath ℂ → ℝ≥0), Measurable τ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        Integrable (stoppedAnnularIncrement P hcirc γ α δ ε τ) (planarBrownianMotion x) ∧
        (∫ b, stoppedAnnularIncrement P hcirc γ α δ ε τ b ∂(planarBrownianMotion x)) ≤
          ((Real.exp (γ^2*Real.log 2)-1) *
            (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂(planarBrownianMotion x)) * 2^d)+1)/2 *
              Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
          2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    ae_brownian_stopped_annular_inserted_increment_le_riesz_energy hh hγ0 hγ2 α x hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro τ hτ ε hε hεhalf hεδ
  let E : ContinuousPath ℂ → ℝ := unitOccupationRieszEnergy d
  let a : ℝ := Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2))
  let c : ℝ := Real.exp (Real.log ε * ((θ-γ)^2/2))
  let B : ℝ := Real.exp (γ^2*Real.log 2)-1
  let G : ContinuousPath ℂ → ℝ := fun b => ((B*(M^2 * E b * 2^d)+1)/2)*a + 2*M*c
  have hE : Integrable E (planarBrownianMotion x) := integrable_unitOccupationRieszEnergy x hd0 hd2
  have hG : Integrable G (planarBrownianMotion x) := by
    dsimp [G]
    fun_prop
  have hm : Measurable (stoppedAnnularIncrement P hcirc γ α δ ε τ) :=
    measurable_stopped_annular_inserted_field_expectation hh hε γ α δ τ hτ
  have hle : ∀ᵐ b ∂(planarBrownianMotion x), stoppedAnnularIncrement P hcirc γ α δ ε τ b ≤ G b := by
    filter_upwards [hb] with b hb
    exact hb (τ b) ε hε hεhalf hεδ
  have hnonneg : ∀ b, 0 ≤ stoppedAnnularIncrement P hcirc γ α δ ε τ b := by
    intro b
    apply integral_nonneg
    intro ω
    exact abs_nonneg _
  have hi : Integrable (stoppedAnnularIncrement P hcirc γ α δ ε τ) (planarBrownianMotion x) := by
    apply hG.mono' hm.aestronglyMeasurable
    filter_upwards [hle] with b hb
    simpa [Real.norm_eq_abs, abs_of_nonneg (hnonneg b)] using hb
  refine ⟨hi, (integral_mono_ae hi hG hle).trans ?_⟩
  change (∫ b, G b ∂(planarBrownianMotion x)) ≤
    ((B*(M^2 * (∫ b, E b ∂(planarBrownianMotion x)) * 2^d)+1)/2)*a + 2*M*c
  have hGeq : G = fun b => (B*M^2*2^d*a/2)*E b + (a/2 + 2*M*c) := by
    funext b
    dsimp [G]
    ring
  rw [hGeq, integral_add (hE.const_mul _) (integrable_const _), integral_const_mul]
  simp only [integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
  ring_nf
  exact le_rfl


/-- The product-law increment estimate is uniform over measurable horizons. -/
theorem lintegral_prod_annular_increment_le_uniform_horizon
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    : ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (τ : ContinuousPath ℂ → ℝ≥0), Measurable τ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        (∫⁻ p : Ω × ContinuousPath ℂ, ENNReal.ofReal
          |annularIncrementSample hcirc γ α δ ε τ p.2 p.1|
          ∂(P.prod (planarBrownianMotion x))) ≤ ENNReal.ofReal (
          ((Real.exp (γ^2*Real.log 2)-1) *
            (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂(planarBrownianMotion x)) * 2^d)+1)/2 *
              Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
          2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_stopped_annular_inserted_increment_annealed_le_uniform_horizon
      hh hγ0 hγ2 α x hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro τ hτ ε hε hεhalf hεδ
  rw [lintegral_prod_annularIncrementSample_eq hh hγ0 hγ2 α x hε hεhalf hεδ τ hτ]
  exact ENNReal.ofReal_le_ofReal (hb τ hτ ε hε hεhalf hεδ).2

/-- The grid reduction remains valid when monotonicity and the cell bound hold
almost everywhere and the grid differences are almost everywhere measurable. -/
theorem lintegral_iSup_abs_sub_le_grid_of_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    (hmono : ∀ᵐ ω ∂μ, MonotoneOn (f ω) (Set.Icc 0 T) ∧
      MonotoneOn (g ω) (Set.Icc 0 T))
    (hgrid : ∀ j : ℕ, AEMeasurable (fun ω => |f ω (j * T / m) - g ω (j * T / m)|) μ)
    (K : Ω → ℝ) (hK : ∀ᵐ ω ∂μ, 0 ≤ K ω ∧
      ∀ j, j < m → g ω ((j + 1) * T / m) - g ω (j * T / m) ≤ K ω) :
    (∫⁻ ω, ⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |f ω t - g ω t| ∂μ) ≤
      (∑ j ∈ Finset.range (m + 1), ∫⁻ ω, ENNReal.ofReal |f ω (j * T / m) - g ω (j * T / m)| ∂μ) +
        ∫⁻ ω, ENNReal.ofReal (K ω) ∂μ := by
  let D : Ω → ℝ := fun ω => ∑ j ∈ Finset.range (m + 1),
    |f ω (j * T / m) - g ω (j * T / m)|
  have hD0 (ω : Ω) : 0 ≤ D ω := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hDm : AEMeasurable D μ := by
    convert Finset.aemeasurable_sum (Finset.range (m + 1)) (fun j _ => hgrid j) using 1
    ext ω
    simp [D]
  have hpoint : ∀ᵐ ω ∂μ,
      (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |f ω t - g ω t|) ≤
        ENNReal.ofReal (D ω) + ENNReal.ofReal (K ω) := by
    filter_upwards [hmono, hK] with ω hω hκ
    apply iSup_le
    intro t
    rw [← ENNReal.ofReal_add (hD0 ω) hκ.1]
    apply ENNReal.ofReal_le_ofReal
    apply LatticeProb.abs_sub_le_of_grid hm hT hω.1 hω.2 ?_ hκ.2 t t.property
    intro j hj
    change |f ω (j * T / m) - g ω (j * T / m)| ≤
      ∑ i ∈ Finset.range (m + 1), |f ω (i * T / m) - g ω (i * T / m)|
    exact Finset.single_le_sum (s := Finset.range (m + 1)) (a := j)
      (f := fun i : ℕ => |f ω (i * T / m) - g ω (i * T / m)|)
      (fun i _ => abs_nonneg (f ω (i * T / m) - g ω (i * T / m)))
      (Finset.mem_range.mpr (by omega))
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (D ω) + ENNReal.ofReal (K ω)) ∂μ := lintegral_mono_ae hpoint
    _ = (∫⁻ ω, ENNReal.ofReal (D ω) ∂μ) + ∫⁻ ω, ENNReal.ofReal (K ω) ∂μ :=
      lintegral_add_left' hDm.ennreal_ofReal _
    _ = _ := by
      congr 1
      simp only [D, ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
      exact lintegral_finsetSum' (Finset.range (m + 1)) (fun j _ => (hgrid j).ennreal_ofReal)

end HarmonicBalls
