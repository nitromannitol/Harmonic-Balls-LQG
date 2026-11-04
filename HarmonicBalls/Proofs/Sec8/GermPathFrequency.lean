import HarmonicBalls.Proofs.Sec8.GermPathErgodic
import HarmonicBalls.Proofs.Sec8.PhaseErgodicFactor
import HarmonicBalls.Proofs.Sec8.BlockFrequency

/-! # Frequencies from stationary local paths

The pointwise ergodic theorem used below is from Leonardo Bonanno's
LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory Filter Finset
open scoped Topology

namespace HarmonicBalls

/-- A bounded phase-dependent observable of an ergodic stationary path has
an almost-sure limiting scale average, with the phase doubled at each step. -/
theorem ae_phase_path_average_of_ergodic_shift
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → E)
    (hXm : ∀ n, Measurable (X n))
    (herg : Ergodic (fun x : ℕ → E => fun n => x (n + 1))
      (P.map (fun ω n => X n ω)))
    (F : PhaseTorus × E → ℝ) (hF : Measurable F)
    (hbound : ∀ p, F p ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Icc 1 N, F ((phaseTorusDouble^[n]) p.1, X n p.2)) / (N : ℝ)) atTop
        (𝓝 (∫ p : PhaseTorus × (ℕ → E), F (p.1, p.2 0)
          ∂(((volume : Measure PhaseCircle).prod volume).prod
            (P.map (fun ω n => X n ω))))) := by
  let Q : Measure PhaseTorus := (volume : Measure PhaseCircle).prod volume
  let path : Ω → ℕ → E := fun ω n => X n ω
  let S : (ℕ → E) → ℕ → E := fun x n => x (n + 1)
  let M : Measure (PhaseTorus × (ℕ → E)) := Q.prod (P.map path)
  let T : PhaseTorus × (ℕ → E) → PhaseTorus × (ℕ → E) :=
    Prod.map phaseTorusDouble S
  let Z : ℕ → PhaseTorus × (ℕ → E) → ℝ := fun n p =>
    F ((phaseTorusDouble^[n]) p.1, p.2 n)
  have hp : Measurable path := Measurable.of_eval hXm
  have hZ : ∀ n, Measurable (Z n) := by
    intro n
    exact hF.comp (((measurePreserving_phaseTorusDouble.measurable.iterate n).comp
      measurable_fst).prodMk ((measurable_pi_apply n).comp measurable_snd))
  have hZb : ∀ n p, Z n p ∈ Set.Icc (0 : ℝ) 1 := fun n p => hbound _
  have hT : Ergodic T M := ergodic_phaseTorusDouble_prod _ _ herg
  have ht : ∀ᵐ p ∂M, ∀ n, Z n (T p) = Z (n + 1) p := by
    filter_upwards with p
    intro n
    dsimp only [Z, T, S, Prod.map]
    rw [Function.iterate_succ_apply]
  have havg := ae_tendsto_initialScaleAverage_of_ae_ergodic_transport M T hT Z hZ hZb ht
  have hmap : (Q.prod P).map (Prod.map id path) = M := by
    dsimp only [M]
    rw [← Measure.map_prod_map Q P measurable_id hp, Measure.map_id]
  have hmeas : Measurable (Prod.map (id : PhaseTorus → PhaseTorus) path) := measurable_id.prodMap hp
  have hconv : ∀ᵐ p ∂((Q.prod P).map (Prod.map id path)),
      Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, Z n p) / (N : ℝ)) atTop
        (𝓝 (∫ p, Z 0 p ∂M)) := by
    rw [hmap]
    exact havg
  have hpull := ae_of_ae_map hmeas.aemeasurable hconv
  simpa only [Prod.map, id_eq, Z, path, Function.iterate_zero, id, M, Q] using hpull

open Classical in
/-- A strict one-scale mean bound yields a block-frequency estimate for the
phase-dependent event evaluated along an ergodic stationary path. -/
theorem ae_phase_path_blockFrequency_of_ergodic_shift
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → E)
    (hXm : ∀ n, Measurable (X n))
    (herg : Ergodic (fun x : ℕ → E => fun n => x (n + 1))
      (P.map (fun ω n => X n ω)))
    (A : Set (PhaseTorus × E)) (hA : MeasurableSet A) (ζ : ℝ)
    (hmean : 1 - ζ < ∫ p : PhaseTorus × (ℕ → E),
      if (p.1, p.2 0) ∈ A then (1 : ℝ) else 0
      ∂(((volume : Measure PhaseCircle).prod volume).prod
        (P.map (fun ω n => X n ω)))) :
    ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Set.Icc (N + 1) (2 * N) ∧
          ((phaseTorusDouble^[n]) p.1, X n p.2) ∈ A}.ncard : ℝ) := by
  let F : PhaseTorus × E → ℝ := fun p => if p ∈ A then 1 else 0
  have hF : Measurable F := measurable_const.piecewise hA measurable_const
  have hb : ∀ p, F p ∈ Set.Icc (0 : ℝ) 1 := by
    intro p
    dsimp only [F]
    split_ifs <;> norm_num
  have hconv := ae_phase_path_average_of_ergodic_shift P X hXm herg F hF hb
  filter_upwards [hconv] with p hp
  apply eventually_goodScale_block_ncard
    (fun n => ((phaseTorusDouble^[n]) p.1, X n p.2) ∈ A) hp
  exact hmean

open Classical in
/-- A stationary local whole-plane GFF path and a strict one-scale mean bound
imply phase-dependent block frequency. -/
theorem IsWholePlaneGFF.ae_phase_path_blockFrequency_of_stationary_local_path
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ)
    (X : ℕ → Ω → E) (hXm : ∀ n, Measurable (X n))
    (hstat : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω))
    (hlocal : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → E,
      (∀ n, K ≤ n → @Measurable Ω E
        (Section6.fieldSigmaAlgebraModConst α₀ hC (Metric.ball 0 ε)) _ (Y n)) ∧
      (∀ n, K ≤ n → X n =ᵐ[P] Y n))
    (A : Set (PhaseTorus × E)) (hA : MeasurableSet A) (ζ : ℝ)
    (hmean : 1 - ζ < ∫ p : PhaseTorus × (ℕ → E),
      if (p.1, p.2 0) ∈ A then (1 : ℝ) else 0
      ∂(((volume : Measure PhaseCircle).prod volume).prod
        (P.map (fun ω n => X n ω)))) :
    ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Set.Icc (N + 1) (2 * N) ∧
          ((phaseTorusDouble^[n]) p.1, X n p.2) ∈ A}.ncard : ℝ) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have herg := ergodic_shift_of_stationary_ae_local_germ P
    (fun ε => Section6.fieldSigmaAlgebraModConst α₀ hC (Metric.ball 0 ε))
    dyadicScale dyadicScale_pos dyadicScale_germ_cofinal.2 dyadicScale_germ_cofinal.1
    (monotone_fieldSigmaAlgebraModConst_ball α₀ hC 0) X hXm hstat hlocal
    (h.origin_germ_trivial α₀)
  exact ae_phase_path_blockFrequency_of_ergodic_shift P X hXm herg A hA ζ hmean

end HarmonicBalls
