import HarmonicBalls.Proofs.Potential.LQGClockAnnularGridBound
import HarmonicBalls.Proofs.Potential.LQGClockAnnularCellSecondMoment

/-! # Uniform annular clock bounds

Grid values and mesh-cell increments control the uniform clock difference.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A grid bound with the maximum of the nonnegative mesh increments. -/
theorem lintegral_iSup_abs_sub_le_grid_and_mesh {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ → ℝ) {m : ℕ} (hm : 0 < m)
    (hmono : ∀ᵐ ω ∂μ, MonotoneOn (f ω) (Icc 0 1) ∧ MonotoneOn (g ω) (Icc 0 1))
    (hgrid : ∀ j : ℕ, AEMeasurable (fun ω => |f ω (j / (m : ℝ)) - g ω (j / (m : ℝ))|) μ) :
    (∫⁻ ω, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |f ω t - g ω t| ∂μ) ≤
      (∑ j ∈ Finset.range (m + 1), ∫⁻ ω, ENNReal.ofReal |f ω (j / (m : ℝ)) - g ω (j / (m : ℝ))| ∂μ) +
      ∫⁻ ω, ⨆ j : Fin m, ENNReal.ofReal (g ω (((j : ℝ) + 1) / m) - g ω ((j : ℝ) / m)) ∂μ := by
  let s := Finset.range m
  have hs : s.Nonempty := ⟨0, Finset.mem_range.mpr hm⟩
  let D : Ω → ℕ → ℝ := fun ω j => g ω ((j + 1) / (m : ℝ)) - g ω (j / (m : ℝ))
  let K : Ω → ℝ := fun ω => s.sup' hs (D ω)
  have hc : ∀ᵐ ω ∂μ, ∀ j, j < m → 0 ≤ D ω j := by
    filter_upwards [hmono] with ω hω j hj
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    have hleft : (j : ℝ) / m ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hm0).2 (by linarith)⟩
    have hright : ((j : ℝ) + 1) / m ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hm0).2 hjm⟩
    exact sub_nonneg.mpr (hω.2 hleft hright (div_le_div_of_nonneg_right (by linarith) hm0.le))
  have hk : ∀ᵐ ω ∂μ, 0 ≤ K ω ∧ ∀ j, j < m → g ω ((j + 1) * 1 / m) - g ω (j * 1 / m) ≤ K ω := by
    filter_upwards [hc] with ω hω
    constructor
    · exact (hω 0 hm).trans (Finset.le_sup' (D ω) (Finset.mem_range.mpr hm))
    · intro j hj
      simpa only [mul_one] using (show D ω j ≤ K ω from Finset.le_sup' (D ω) (Finset.mem_range.mpr hj))
  have hmax : ∀ᵐ ω ∂μ, ENNReal.ofReal (K ω) = ⨆ j : Fin m, ENNReal.ofReal (D ω j) := by
    filter_upwards with ω
    apply le_antisymm
    · obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' hs (D ω)
      rw [show K ω = D ω j from heq]
      exact le_iSup (fun i : Fin m => ENNReal.ofReal (D ω i)) ⟨j, Finset.mem_range.mp hj⟩
    · refine iSup_le fun j => ENNReal.ofReal_le_ofReal ?_
      exact Finset.le_sup' (D ω) (Finset.mem_range.mpr j.isLt)
  have hbase := lintegral_iSup_abs_sub_le_grid_of_ae μ f g (T := 1) (by norm_num) hm hmono (by simpa using hgrid) K hk
  simpa only [mul_one, lintegral_congr_ae hmax] using hbase


/-- Actual dyadic annular clock differences are controlled by their grid
values and the maximum mass of a mesh cell at the coarser scale. -/
theorem lintegral_prod_stoppedAnnularClock_iSup_le_grid_and_mesh
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) (γ α δ : ℝ)
    (k m : ℕ) (hm : 0 < m) :
    let F : ℕ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun n p t =>
      stoppedAnnularClock (fun z => (dyadicScale n)^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale n) z)) δ
        (fun _ => t.toNNReal) p.2
    (∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F (k+1) p t - F k p t|
      ∂(P.prod (planarBrownianMotion x))) ≤
      (∑ j ∈ Finset.range (m + 1), ∫⁻ p, ENNReal.ofReal
        |F (k+1) p (j / (m : ℝ)) - F k p (j / (m : ℝ))|
        ∂(P.prod (planarBrownianMotion x))) +
      ∫⁻ p : Ω × ContinuousPath ℂ, (⨆ j : Fin m, ∫⁻ t in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
        ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale k)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale k) z))
              (p.2 t.toNNReal))) ∂(P.prod (planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  dsimp only
  let F : ℕ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun n p t =>
    stoppedAnnularClock (fun z => (dyadicScale n)^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale n) z)) δ
      (fun _ => t.toNNReal) p.2
  have hmono : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)),
      MonotoneOn (F (k+1) p) (Icc 0 1) ∧ MonotoneOn (F k p) (Icc 0 1) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_dyadic_stoppedAnnularClock_monotone_and_cell hh γ α δ)] with p hp
    exact ⟨(hp (k+1) p.2).1, (hp k p.2).1⟩
  have hgrid (j : ℕ) : AEMeasurable (fun p => |F (k+1) p (j / (m : ℝ)) -
      F k p (j / (m : ℝ))|) (P.prod (planarBrownianMotion x)) := by
    exact (aemeasurable_stoppedAnnularClock_sub hh x γ α δ
      (fun _ => (j / (m : ℝ)).toNNReal) measurable_const k).abs
  have hcell : (fun p : Ω × ContinuousPath ℂ => ⨆ j : Fin m,
      ENNReal.ofReal (F k p (((j : ℝ) + 1) / m) - F k p ((j : ℝ) / m))) =ᵐ[
        P.prod (planarBrownianMotion x)] (fun p => ⨆ j : Fin m,
      ∫⁻ t in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m), ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale k)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale k) z))
              (p.2 t.toNNReal))) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_dyadic_stoppedAnnularClock_monotone_and_cell hh γ α δ)] with p hp
    apply iSup_congr
    intro j
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast j.isLt
    exact (hp k p.2).2 (by positivity) (div_le_div_of_nonneg_right (by linarith) hm0.le)
      ((div_le_one hm0).2 hjm)
  have h := lintegral_iSup_abs_sub_le_grid_and_mesh (P.prod (planarBrownianMotion x))
    (F (k+1)) (F k) hm hmono hgrid
  rw [lintegral_congr_ae hcell] at h
  exact h


/-- In the second-moment range, the uniform dyadic clock difference is
bounded by the sum of the fixed-horizon rate and a mesh oscillation rate. -/
theorem exists_lintegral_prod_stoppedAnnularClock_iSup_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (θ d M : ℝ) (C : ℝ≥0∞) (β : ℝ), γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧ C < ∞ ∧ 0 < β ∧
      ∀ (k m : ℕ), 0 < m → dyadicScale k ≤ 1/2 → dyadicScale k ≤ δ →
        (∫⁻ p : Ω × ContinuousPath ℂ, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal (|stoppedAnnularClock (fun z => (dyadicScale (k+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) δ
              (fun _ => ((t : ℝ).toNNReal)) p.2 -
          stoppedAnnularClock (fun z => (dyadicScale k)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale k) z)) δ
              (fun _ => ((t : ℝ).toNNReal)) p.2|) ∂(P.prod (planarBrownianMotion x))) ≤
        (∑ _j ∈ Finset.range (m+1), ENNReal.ofReal (
          ((Real.exp (γ^2*Real.log 2)-1) *
            (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂(planarBrownianMotion x)) * 2^d)+1)/2 *
              Real.exp (Real.log (dyadicScale k) * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
          2*M*Real.exp (Real.log (dyadicScale k) * ((θ-γ)^2/2)))) +
          C * (m : ℝ≥0∞) ^ (-β) := by
  have hγlt : γ < 2 := by nlinarith [sq_nonneg (γ - 1)]
  obtain ⟨θ, d, M, hθ1, hθ2, hd0, hd2, hp, hM, hgrid⟩ :=
    lintegral_prod_stoppedAnnularClock_sub_le_uniform_horizon hh hγ hγlt α x hδ
  obtain ⟨C, β, hC, hβ, hmesh⟩ :=
    exists_lintegral_prod_annular_mesh_max_le hh x hγ.ne' hγ2 α δ
  refine ⟨θ, d, M, C, β, hθ1, hθ2, hd0, hd2, hp, hM, hC, hβ, ?_⟩
  intro k m hm hkhalf hkδ
  apply (lintegral_prod_stoppedAnnularClock_iSup_le_grid_and_mesh hh x γ α δ k m hm).trans
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j hj
    exact hgrid (fun _ => (j / (m : ℝ)).toNNReal) measurable_const k hkhalf hkδ
  · exact hmesh (dyadicScale_pos k) hkδ m hm

end HarmonicBalls
