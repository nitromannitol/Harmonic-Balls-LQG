import HarmonicBalls.Proofs.Potential.LQGClockAnnularSupremum
import Mathlib.Analysis.PSeries

/-! # Summability of annular clock increments

Polynomial time meshes yield a summable bound for fine dyadic scales.
-/

open MeasureTheory MarkovProcess Filter Set
open scoped ENNReal NNReal Topology

namespace HarmonicBalls

private theorem mesh_rates (N : ℕ) {r β : ℝ} (hr : 0 < r) (hβ : 1 < N * β) :
    Summable (fun k : ℕ => (((k+1 : ℕ) : ℝ)^N + 1) * Real.exp (-r * (k : ℝ))) ∧
    Summable (fun k : ℕ => (((k+1 : ℕ) : ℝ)^N) ^ (-β)) := by
  constructor
  · have h1 := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul N hr)
    have h2 := Real.summable_pow_mul_exp_neg_nat_mul 0 hr
    have heq : ∀ k : ℕ, (((k+1 : ℕ) : ℝ)^N + 1) * Real.exp (-r * (k : ℝ)) =
        Real.exp r * (((k+1 : ℕ) : ℝ)^N * Real.exp (-r * ((k+1 : ℕ) : ℝ))) +
          ((k : ℝ)^0 * Real.exp (-r * (k : ℝ))) := by
      intro k
      have hexp : Real.exp r * Real.exp (-r * ((k+1 : ℕ) : ℝ)) = Real.exp (-r * (k : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      calc
        _ = ((k+1 : ℕ) : ℝ)^N * (Real.exp r * Real.exp (-r * ((k+1 : ℕ) : ℝ))) + Real.exp (-r * (k : ℝ)) := by rw [hexp]; ring
        _ = _ := by simp only [pow_zero, one_mul]; ring
    simp_rw [heq]
    exact (h1.mul_left _).add h2
  · have h := (Real.summable_nat_rpow.mpr (show -(N * β) < -1 by linarith))
    have h := (summable_nat_add_iff 1).2 h
    convert h using 1
    funext k
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ((k+1 : ℕ) : ℝ))]
    congr 1
    ring

private theorem choose_mesh {β : ℝ} (hβ : 0 < β) : ∃ N : ℕ, 1 < (N : ℝ) * β := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / β)
  exact ⟨N, (div_lt_iff₀ hβ).mp hN⟩

private theorem mesh_power (N : ℕ) {β : ℝ} (hβ : 1 < N * β) :
    (∑' k : ℕ, ((k+1 : ℕ)^N : ℝ≥0∞) ^ (-β)) < ⊤ := by
  have hs := (show Summable (fun k : ℕ => (((k+1 : ℕ) : ℝ)^N) ^ (-β)) from by
    have h := (Real.summable_nat_rpow.mpr (show -(N * β) < -1 by linarith))
    have h := (summable_nat_add_iff 1).2 h
    convert h using 1
    funext k
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ((k+1 : ℕ) : ℝ))]
    congr 1
    ring).tsum_ofReal_lt_top
  convert hs using 1
  congr 1
  funext k
  rw [← ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < ((k+1 : ℕ) : ℝ)^N)]
  congr 1
  norm_cast

private theorem balanced_rates (N : ℕ) {r s β : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hβ : 1 < N * β) (A B : ℝ) {C : ℝ≥0∞} (hC : C < ⊤) :
    (∑' k : ℕ, (ENNReal.ofReal (((((k+1 : ℕ) : ℝ)^N) + 1) *
      (A * Real.exp (-r * k) + B * Real.exp (-s * k))) +
      C * ((k+1 : ℕ)^N : ℝ≥0∞)^(-β))) < ⊤ := by
  have ha := ((mesh_rates N hr hβ).1).mul_left A
  have hb := ((mesh_rates N hs hβ).1).mul_left B
  have hsum : Summable (fun k : ℕ => (((((k+1 : ℕ) : ℝ)^N) + 1) *
      (A * Real.exp (-r * k) + B * Real.exp (-s * k)))) := by
    convert ha.add hb using 1
    funext k
    ring
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
  exact ENNReal.add_lt_top.mpr ⟨hsum.tsum_ofReal_lt_top, ENNReal.mul_lt_top hC (mesh_power N hβ)⟩

/-- Fine-scale expected uniform annular clock increments have finite sum in the
second-moment range. -/
theorem exists_tsum_lintegral_prod_stoppedAnnularClock_iSup_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, (∑' j : ℕ, ∫⁻ p : Ω × ContinuousPath ℂ,
      ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal (|stoppedAnnularClock (fun z =>
        (dyadicScale (j+K+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K+1)) z)) δ
            (fun _ => ((t : ℝ).toNNReal)) p.2 -
        stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
            (fun _ => ((t : ℝ).toNNReal)) p.2|) ∂(P.prod (planarBrownianMotion x))) < ⊤ := by
  obtain ⟨θ, d, M, C, β, hθ1, hθ2, hd0, hd2, hp, hM, hC, hβ, hbound⟩ :=
    exists_lintegral_prod_stoppedAnnularClock_iSup_le hh x hγ hγ2 α hδ
  obtain ⟨N, hN⟩ := choose_mesh hβ
  let A : ℝ := ((Real.exp (γ^2*Real.log 2)-1) *
    (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂(planarBrownianMotion x)) * 2^d)+1)/2
  let B : ℝ := 2*M
  let r : ℝ := Real.log 2 * ((d-γ^2+(2*γ-θ)^2/2)/2)
  let s : ℝ := Real.log 2 * ((θ-γ)^2/2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hseries := balanced_rates N hr hs hN A B hC
  have ht : Tendsto dyadicScale atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hcut : 0 < min (1/2 : ℝ) δ := lt_min (by norm_num) hδ
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds hcut))
  refine ⟨K, ?_⟩
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum (g := fun j : ℕ =>
    ENNReal.ofReal (((((j+K+1 : ℕ) : ℝ)^N) + 1) *
      (A * Real.exp (-r * (j+K : ℕ)) + B * Real.exp (-s * (j+K : ℕ)))) +
      C * ((j+K+1 : ℕ)^N : ℝ≥0∞)^(-β)) (fun j => ?_)) ?_
  · let k := j+K
    let m := (k+1)^N
    have hm : 0 < m := by dsimp [m]; positivity
    have hk : dyadicScale k < min (1/2) δ := hK k (by dsimp [k]; omega)
    have h := hbound k m hm (le_of_lt (lt_of_lt_of_le hk (min_le_left _ _)))
      (le_of_lt (lt_of_lt_of_le hk (min_le_right _ _)))
    have hlog : Real.log (dyadicScale k) = -((k : ℝ) * Real.log 2) := by
      rw [dyadicScale, Real.log_pow, Real.log_inv]
      ring
    have hrw : Real.exp (Real.log (dyadicScale k) * ((d-γ^2+(2*γ-θ)^2/2)/2)) =
        Real.exp (-r * k) := by rw [hlog]; congr 1; dsimp [r]; ring
    have hsw : Real.exp (Real.log (dyadicScale k) * ((θ-γ)^2/2)) =
        Real.exp (-s * k) := by rw [hlog]; congr 1; dsimp [s]; ring
    rw [hrw, hsw] at h
    have hsum (v : ℝ) : (∑ _j ∈ Finset.range (m+1), ENNReal.ofReal v) =
        ENNReal.ofReal (((m : ℝ) + 1) * v) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast (m+1),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((m+1 : ℕ) : ℝ))]
      push_cast
      rfl
    rw [hsum] at h
    simpa only [m, k, Nat.cast_pow, Nat.cast_add, Nat.cast_one, A, B] using h
  · exact (ENNReal.tsum_comp_le_tsum_of_injective (f := fun j : ℕ => j+K)
      (by intro a b h; exact Nat.add_right_cancel h) _).trans_lt hseries

end HarmonicBalls
