import HarmonicBalls.Proofs.Sec8.InteriorRadialIndependence
import HarmonicBalls.Proofs.Sec8.CircleAverageBrownian

/-! # Interior field and earlier radial increments -/

open MeasureTheory ProbabilityTheory Metric Set

namespace HarmonicBalls

/-- Zero-integral test pairings in the disk of radius `exp(-N)` are jointly
independent of all the radial increments before logarithmic time `N`. -/
theorem IsWholePlaneGFF.indepFun_interiorPairings_earlierRadialIncrements
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (N : ℕ) :
    IndepFun
      (fun ω (φ : {φ : ℂ → ℝ // IsTestFunction
          (closedBall (0 : ℂ) (Real.exp (-(N : ℝ)))) φ ∧ ∫ x, φ x = 0}) => hC ω φ.1)
      (fun ω (k : Fin N) => radialCircleIncrement hcirc k.1 ω) P := by
  let R := Real.exp (-(N : ℝ))
  let T := {r : ℝ // R ≤ r ∧ r ≤ 1}
  have hr (k : ℕ) (hk : k ≤ N) :
      R ≤ Real.exp (-(k : ℝ)) ∧ Real.exp (-(k : ℝ)) ≤ 1 := by
    constructor
    · apply Real.exp_le_exp.mpr
      exact neg_le_neg (by exact_mod_cast hk)
    · rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg k))
  let lo : Fin N → T := fun k => ⟨_, hr k.1 (Nat.le_of_lt k.2)⟩
  let hi : Fin N → T := fun k => ⟨_, hr (k.1 + 1) k.2⟩
  let F : (T → ℝ) → Fin N → ℝ := fun f k => f (hi k) - f (lo k)
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro k
    exact (measurable_pi_apply (hi k)).sub (measurable_pi_apply (lo k))
  have hind := (h.indepFun_interiorPairings_exteriorCircleAverages (Real.exp_pos (-(N : ℝ)))).comp
    measurable_id hF
  simpa only [Function.comp_def, id_eq, F, hi, lo, radialCircleIncrement, radialCircleAverage,
    Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using hind

/-- An event measurable with respect to the zero-integral field in every
shrinking disk is independent of the entire radial increment process. -/
theorem IsWholePlaneGFF.indep_radialIncrements_of_interiorPairingGerm
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (A : Set Ω)
    (hA : ∀ N : ℕ, MeasurableSet[MeasurableSpace.comap
      (fun ω (φ : {φ : ℂ → ℝ // IsTestFunction
        (closedBall (0 : ℂ) (Real.exp (-(N : ℝ)))) φ ∧ ∫ x, φ x = 0}) => hC ω φ.1)
      inferInstance] A) :
    Indep (⨆ n : ℕ, MeasurableSpace.comap (radialCircleIncrement hcirc n) inferInstance)
      (MeasurableSpace.generateFrom {A}) P := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let m : ℕ → MeasurableSpace Ω := fun N => MeasurableSpace.comap
    (fun ω (k : Fin N) => radialCircleIncrement hcirc k.1 ω) inferInstance
  have hmform (N : ℕ) : m N = ⨆ k : Fin N,
      MeasurableSpace.comap (radialCircleIncrement hcirc k.1) inferInstance := by
    exact MeasurableSpace.comap_process_pi _
  have hmono : Monotone m := by
    intro a b hab
    rw [hmform, hmform]
    apply iSup_le
    intro k
    exact le_iSup_of_le ⟨k.1, lt_of_lt_of_le k.2 hab⟩ le_rfl
  have hle : ∀ N, m N ≤ mΩ := by
    intro N
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro k
    exact (h.measurable_circle _ _ (Real.exp_pos _)).sub
      (h.measurable_circle _ _ (Real.exp_pos _))
  have hgen : MeasurableSpace.generateFrom {A} ≤ mΩ :=
    (MeasurableSpace.generateFrom_singleton_le (hA 0)).trans
      (Measurable.comap_le (Measurable.of_eval (fun φ =>
        h.measurable_pairing φ.1 ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩)))
  have hind : ∀ N, Indep (m N) (MeasurableSpace.generateFrom {A}) P := by
    intro N
    apply indep_of_indep_of_le_right ((IndepFun_iff_Indep _ _ _).mp (h.indepFun_interiorPairings_earlierRadialIncrements N)).symm
    exact MeasurableSpace.generateFrom_singleton_le (hA N)
  have hs := indep_iSup_of_monotone hind hle hgen hmono
  have heq : (⨆ N, m N) = ⨆ n : ℕ,
      MeasurableSpace.comap (radialCircleIncrement hcirc n) inferInstance := by
    apply le_antisymm
    · apply iSup_le
      intro N
      rw [hmform]
      exact iSup_le fun k => le_iSup (fun n : ℕ =>
        MeasurableSpace.comap (radialCircleIncrement hcirc n) inferInstance) k.1
    · apply iSup_le
      intro n
      calc
        MeasurableSpace.comap (radialCircleIncrement hcirc n) inferInstance ≤ m (n + 1) := by
          rw [hmform]
          exact le_iSup (fun k : Fin (n + 1) =>
            MeasurableSpace.comap (radialCircleIncrement hcirc k.1) inferInstance)
            ⟨n, Nat.lt_succ_self n⟩
        _ ≤ ⨆ N, m N := le_iSup m (n + 1)
  rw [← heq]
  exact hs

end HarmonicBalls
