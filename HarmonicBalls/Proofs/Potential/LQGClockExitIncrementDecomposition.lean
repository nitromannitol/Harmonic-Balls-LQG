import HarmonicBalls.Proofs.Potential.LQGClockExpectationConvergence
import HarmonicBalls.Proofs.Potential.GreenOccupationCharacterization

/-! # Exit-time clock increments from unit-horizon increments

For a bounded open domain `D`, an interval integral along a path up to its exit time from `D`
splits at the integer times into unit-horizon pieces of the shifted paths, each counted only
while the path has not yet left `D`. By the simple Markov property of planar Brownian motion,
a bound on the expected unit-horizon stopped increments, uniform over starting points in `D`,
bounds the expected exit-time increment by the same constant times `1 + E τ_D`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- Simple Markov property of planar Brownian motion at a deterministic time, for events of
the canonical filtration and nonnegative functionals of the shifted path. -/
theorem setLIntegral_shift_planarBrownianMotion (x : ℂ) (s : ℝ≥0)
    {A : Set (ContinuousPath ℂ)}
    (hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) s] A)
    {G : ContinuousPath ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ b in A, G (ContinuousPath.shift s b) ∂(planarBrownianMotion x) =
      ∫⁻ b in A, (∫⁻ b', G b' ∂(planarBrownianMotion (b s))) ∂(planarBrownianMotion x) := by
  have hK := planarBrownianMotion_eq_continuousProcess
  have hrestart :=
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup x s A hA
  rw [← hK] at hrestart
  rw [← lintegral_map hG (ContinuousPath.measurable_shift_fixed s), hrestart,
    Measure.lintegral_bind (Kernel.aemeasurable _) hG.aemeasurable]
  rfl

/-- Translating time by a shift of the path. -/
theorem intervalIntegral_shift_path (g : ℂ → ℝ) (b : ContinuousPath ℂ) (t : ℝ≥0) {u : ℝ}
    (hu : 0 ≤ u) :
    (∫ s in (t : ℝ)..(t : ℝ) + u, g (b s.toNNReal)) =
      ∫ s in (0 : ℝ)..u, g ((ContinuousPath.shift t b) s.toNNReal) := by
  have h := intervalIntegral.integral_comp_add_right (fun s : ℝ => g (b s.toNNReal))
    (a := 0) (b := u) (t : ℝ)
  rw [zero_add, add_comm u] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hu] at hs
  have hst : (s + (t : ℝ)).toNNReal = t + s.toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal _ hs.1,
      Real.coe_toNNReal _ (add_nonneg hs.1 (NNReal.coe_nonneg t))]
    ring
  simp only [ContinuousPath.shift_apply]
  congr 2

private theorem lt_exitTime_iff_lt_toReal {e : ℝ≥0∞} (he : e ≠ ⊤) (n : ℕ) :
    (((n : ℝ≥0) : ℝ≥0∞) < e) ↔ (n : ℝ) < e.toReal := by
  rw [ENNReal.coe_natCast, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_lt_iff_lt_toReal (Nat.cast_nonneg n) he

/-- An interval integral up to a finite exit time is bounded by the sum over integer times
of the unit-horizon integrals of the shifted paths that have not yet exited. -/
theorem ofReal_abs_integral_exit_le_tsum (D : Set ℂ) (g : ℂ → ℝ) (b : ContinuousPath ℂ)
    (hg : ∀ u v : ℝ, IntervalIntegrable (fun s : ℝ => g (b s.toNNReal)) volume u v)
    (hb : ContinuousPath.exitTime D b ≠ ⊤) :
    ENNReal.ofReal |∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, g (b s.toNNReal)| ≤
      ∑' n : ℕ, {b' : ContinuousPath ℂ | ((n : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b'}.indicator
        (fun b' => ENNReal.ofReal |∫ s in (0 : ℝ)..min 1
          (ContinuousPath.exitTime D (ContinuousPath.shift (n : ℝ≥0) b')).toReal,
            g ((ContinuousPath.shift (n : ℝ≥0) b') s.toNNReal)|) b := by
  set τ := (ContinuousPath.exitTime D b).toReal with hτdef
  have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
  let f : ℝ → ℝ := fun s => g (b s.toNNReal)
  let N : ℕ := ⌈τ⌉₊
  let a : ℕ → ℝ := fun n => min (n : ℝ) τ
  have ha0 : a 0 = 0 := by simp [a, hτ0]
  have haN : a N = τ := min_eq_right (Nat.le_ceil τ)
  have hsum : (∑ k ∈ Finset.range N, ∫ s in a k..a (k+1), f s) = ∫ s in a 0..a N, f s :=
    intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hg _ _)
  let T : ℕ → ℝ≥0∞ := fun n =>
    {b' : ContinuousPath ℂ | ((n : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b'}.indicator
      (fun b' => ENNReal.ofReal |∫ s in (0 : ℝ)..min 1
        (ContinuousPath.exitTime D (ContinuousPath.shift (n : ℝ≥0) b')).toReal,
          g ((ContinuousPath.shift (n : ℝ≥0) b') s.toNNReal)|) b
  have hpiece (k : ℕ) : ENNReal.ofReal |∫ s in a k..a (k+1), f s| ≤ T k := by
    by_cases hk : (k : ℝ) < τ
    · have hlt : ((k : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b :=
        (lt_exitTime_iff_lt_toReal hb k).mpr hk
      have hshift := ContinuousPath.exitTime_shift_add D b (k : ℝ≥0) hlt
      have hne : ContinuousPath.exitTime D (ContinuousPath.shift (k : ℝ≥0) b) ≠ ⊤ := by
        intro htop
        rw [htop, top_add] at hshift
        exact hb hshift.symm
      have hreal : (ContinuousPath.exitTime D (ContinuousPath.shift (k : ℝ≥0) b)).toReal =
          τ - k := by
        have h := congrArg ENNReal.toReal hshift
        rw [ENNReal.toReal_add hne ENNReal.coe_ne_top] at h
        simp only [ENNReal.coe_toReal, NNReal.coe_natCast] at h
        rw [hτdef, ← h]
        ring
      have hak : a k = k := min_eq_left hk.le
      have hak1 : a (k+1) = (k : ℝ) + min 1 (τ - k) := by
        simp only [a, Nat.cast_add, Nat.cast_one]
        rw [← min_add_add_left]
        congr 1
        ring
      have hT : T k = ENNReal.ofReal |∫ s in (0 : ℝ)..min 1
          (ContinuousPath.exitTime D (ContinuousPath.shift (k : ℝ≥0) b)).toReal,
            g ((ContinuousPath.shift (k : ℝ≥0) b) s.toNNReal)| := by
        simp only [T]
        rw [Set.indicator_of_mem (show b ∈ {b' : ContinuousPath ℂ |
          ((k : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b'} from hlt)]
      rw [hT, hreal, hak, hak1]
      have hu : 0 ≤ min 1 (τ - k) := le_min zero_le_one (by linarith)
      have h := intervalIntegral_shift_path g b (k : ℝ≥0) hu
      simp only [NNReal.coe_natCast] at h
      rw [h]
    · have hak : a k = τ := min_eq_right (not_lt.mp hk)
      have hak1 : a (k+1) = τ := by
        simp only [a]
        apply min_eq_right
        push_cast
        linarith [not_lt.mp hk]
      rw [hak, hak1, intervalIntegral.integral_same, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
  have hmain : (∫ s in (0 : ℝ)..τ, f s) = ∑ k ∈ Finset.range N, ∫ s in a k..a (k+1), f s := by
    rw [hsum, ha0, haN]
  calc
    ENNReal.ofReal |∫ s in (0 : ℝ)..τ, g (b s.toNNReal)|
        = ENNReal.ofReal |∑ k ∈ Finset.range N, ∫ s in a k..a (k+1), f s| := by
      rw [← hmain]
    _ ≤ ENNReal.ofReal (∑ k ∈ Finset.range N, |∫ s in a k..a (k+1), f s|) :=
      ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ k ∈ Finset.range N, ENNReal.ofReal |∫ s in a k..a (k+1), f s| :=
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)
    _ ≤ ∑ k ∈ Finset.range N, T k := Finset.sum_le_sum (fun k _ => hpiece k)
    _ ≤ ∑' n : ℕ, T n := ENNReal.sum_le_tsum _

/-- The number of integer times before a time in `[0, ∞]` is at most that time plus one. -/
theorem tsum_indicator_natCast_lt_le (e : ℝ≥0∞) :
    (∑' n : ℕ, {e' : ℝ≥0∞ | ((n : ℝ≥0) : ℝ≥0∞) < e'}.indicator (fun _ => (1 : ℝ≥0∞)) e) ≤
      e + 1 := by
  rcases eq_or_ne e ⊤ with rfl | he
  · simp
  · set r := e.toReal
    have hr : 0 ≤ r := ENNReal.toReal_nonneg
    have hiff (n : ℕ) : ((n : ℝ≥0) : ℝ≥0∞) < e ↔ n ∈ Finset.range ⌈r⌉₊ := by
      rw [lt_exitTime_iff_lt_toReal he n, Finset.mem_range, Nat.lt_ceil]
    rw [tsum_eq_sum (s := Finset.range ⌈r⌉₊)]
    · have hval : ∀ n ∈ Finset.range ⌈r⌉₊,
          {e' : ℝ≥0∞ | ((n : ℝ≥0) : ℝ≥0∞) < e'}.indicator (fun _ => (1 : ℝ≥0∞)) e = 1 := by
        intro n hn
        exact Set.indicator_of_mem (show e ∈ {e' : ℝ≥0∞ | ((n : ℝ≥0) : ℝ≥0∞) < e'} from
          (hiff n).mpr hn) _
      rw [Finset.sum_congr rfl hval, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have hc : ((⌈r⌉₊ : ℝ)) ≤ r + 1 := (Nat.ceil_lt_add_one hr).le
      calc
        ((⌈r⌉₊ : ℕ) : ℝ≥0∞) = ENNReal.ofReal (⌈r⌉₊ : ℝ) := (ENNReal.ofReal_natCast _).symm
        _ ≤ ENNReal.ofReal (r + 1) := ENNReal.ofReal_le_ofReal hc
        _ = e + 1 := by
          rw [ENNReal.ofReal_add hr zero_le_one, ENNReal.ofReal_toReal he, ENNReal.ofReal_one]
    · intro n hn
      exact Set.indicator_of_notMem (show e ∉ {e' : ℝ≥0∞ | ((n : ℝ≥0) : ℝ≥0∞) < e'} from
        fun h => hn ((hiff n).mp h)) _

/-- Interval integrals along a path up to a nonnegative measurable time are jointly measurable
in a parameter and the path. -/
theorem measurable_intervalIntegral_path {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω × ℂ → ℝ) (hF : Measurable F) (u : ContinuousPath ℂ → ℝ) (hu : Measurable u)
    (hu0 : ∀ b, 0 ≤ u b) :
    Measurable (fun p : Ω × ContinuousPath ℂ =>
      ∫ s in (0 : ℝ)..u p.2, F (p.1, p.2 s.toNNReal)) := by
  let G : (Ω × ContinuousPath ℂ) × ℝ → ℝ := fun q =>
    if 0 < q.2 ∧ q.2 ≤ u q.1.2 then F (q.1.1, q.1.2 q.2.toNNReal) else 0
  have heval : Measurable (fun q : ContinuousPath ℂ × ℝ≥0 => q.1 q.2) := by fun_prop
  have hFG : Measurable (fun q : (Ω × ContinuousPath ℂ) × ℝ => F (q.1.1, q.1.2 q.2.toNNReal)) :=
    hF.comp ((measurable_fst.comp measurable_fst).prodMk
      (heval.comp ((measurable_snd.comp measurable_fst).prodMk
        (continuous_real_toNNReal.measurable.comp measurable_snd))))
  have hset : MeasurableSet {q : (Ω × ContinuousPath ℂ) × ℝ | 0 < q.2 ∧ q.2 ≤ u q.1.2} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hu.comp (measurable_snd.comp measurable_fst)))
  have hGm : StronglyMeasurable G := (Measurable.ite hset hFG measurable_const).stronglyMeasurable
  have hint := hGm.integral_prod_right' (ν := (volume : Measure ℝ))
  have heq : (fun p : Ω × ContinuousPath ℂ => ∫ s in (0 : ℝ)..u p.2, F (p.1, p.2 s.toNNReal)) =
      fun p => ∫ s, G (p, s) := by
    funext p
    rw [intervalIntegral.integral_of_le (hu0 p.2), ← integral_indicator measurableSet_Ioc]
    congr 1
    funext s
    simp only [G, Set.indicator_apply, Set.mem_Ioc]
  rw [heq]
  exact hint.measurable

/-- A bound on the expected unit-horizon stopped increments, uniform over starting points in
`D`, bounds the expected increment up to the exit time by the same constant times
`1 + E τ_D`. -/
theorem lintegral_ofReal_abs_exit_integral_le_of_unit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {D : Set ℂ} (hD : IsOpen D) (x : ℂ) (F : Ω × ℂ → ℝ) (hF : Measurable F)
    (hFi : ∀ (ω : Ω) (b : ContinuousPath ℂ) (u v : ℝ),
      IntervalIntegrable (fun s : ℝ => F (ω, b s.toNNReal)) volume u v) (c : ℝ≥0∞)
    (hc : ∀ y ∈ D, (∫⁻ p, ENNReal.ofReal |∫ s in (0 : ℝ)..min 1
        (ContinuousPath.exitTime D p.2).toReal, F (p.1, p.2 s.toNNReal)|
        ∂(P.prod (planarBrownianMotion y))) ≤ c)
    (hfin : ∀ᵐ b ∂(planarBrownianMotion x), ContinuousPath.exitTime D b ≠ ⊤) :
    (∫⁻ p, ENNReal.ofReal |∫ s in (0 : ℝ)..(ContinuousPath.exitTime D p.2).toReal,
        F (p.1, p.2 s.toNNReal)| ∂(P.prod (planarBrownianMotion x))) ≤
      c * ∫⁻ b, (ContinuousPath.exitTime D b + 1) ∂(planarBrownianMotion x) := by
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime D
  have hτm : Measurable τ := ContinuousPath.measurable_exitTime D hD
  let h : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |∫ s in (0 : ℝ)..min 1 (τ p.2).toReal, F (p.1, p.2 s.toNNReal)|
  have hhm : Measurable h :=
    ((measurable_intervalIntegral_path F hF (fun b => min 1 (τ b).toReal)
      (measurable_const.min hτm.ennreal_toReal)
      (fun _ => le_min zero_le_one ENNReal.toReal_nonneg)).abs).ennreal_ofReal
  let A : ℕ → Set (ContinuousPath ℂ) := fun n => {b | ((n : ℝ≥0) : ℝ≥0∞) < τ b}
  have hAc (n : ℕ) : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) (n : ℝ≥0)]
      (A n) := ContinuousPath.measurableSet_lt_exitTime_canonicalFiltration D hD _
  have hAm (n : ℕ) : MeasurableSet (A n) := ContinuousPath.measurableSet_lt_exitTime D hD _
  let term : ℕ → Ω × ContinuousPath ℂ → ℝ≥0∞ := fun n p =>
    (Prod.snd ⁻¹' A n).indicator (fun p => h (p.1, ContinuousPath.shift (n : ℝ≥0) p.2)) p
  have htermm (n : ℕ) : Measurable (term n) :=
    (hhm.comp (measurable_fst.prodMk
      ((ContinuousPath.measurable_shift_fixed _).comp measurable_snd))).indicator
      (measurable_snd (hAm n))
  have hpoint : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)),
      ENNReal.ofReal |∫ s in (0 : ℝ)..(τ p.2).toReal, F (p.1, p.2 s.toNNReal)| ≤
        ∑' n, term n p := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := P)
      (ν := planarBrownianMotion x)).ae hfin] with p hp
    have h := ofReal_abs_integral_exit_le_tsum D (fun z => F (p.1, z)) p.2 (hFi p.1 p.2) hp
    refine h.trans (le_of_eq ?_)
    congr 1
  have hn (n : ℕ) : (∫⁻ p, term n p ∂(P.prod (planarBrownianMotion x))) ≤
      c * planarBrownianMotion x (A n) := by
    rw [lintegral_prod_symm _ (htermm n).aemeasurable]
    have hinner (b : ContinuousPath ℂ) : (∫⁻ ω, term n (ω, b) ∂P) =
        (A n).indicator (fun b => ∫⁻ ω, h (ω, ContinuousPath.shift (n : ℝ≥0) b) ∂P) b := by
      by_cases hb : b ∈ A n
      · rw [Set.indicator_of_mem hb]
        apply lintegral_congr
        intro ω
        exact Set.indicator_of_mem (show (ω, b) ∈ Prod.snd ⁻¹' A n from hb) _
      · rw [Set.indicator_of_notMem hb]
        have hz : ∀ ω, term n (ω, b) = 0 := fun ω =>
          Set.indicator_of_notMem (show (ω, b) ∉ Prod.snd ⁻¹' A n from hb) _
        simp only [hz, lintegral_zero]
    simp_rw [hinner]
    rw [lintegral_indicator (hAm n)]
    have hG : Measurable (fun b' : ContinuousPath ℂ => ∫⁻ ω, h (ω, b') ∂P) :=
      hhm.lintegral_prod_left'
    rw [setLIntegral_shift_planarBrownianMotion x (n : ℝ≥0) (hAc n) hG]
    calc
      (∫⁻ b in A n, ∫⁻ b', ∫⁻ ω, h (ω, b') ∂P ∂(planarBrownianMotion (b (n : ℝ≥0)))
          ∂(planarBrownianMotion x)) ≤ ∫⁻ _b in A n, c ∂(planarBrownianMotion x) := by
        apply setLIntegral_mono measurable_const
        intro b hb
        have hmem : b (n : ℝ≥0) ∈ D := ContinuousPath.mem_of_lt_exitTime D b _ hb
        rw [← lintegral_prod_symm' _ hhm]
        exact hc _ hmem
      _ = c * planarBrownianMotion x (A n) := setLIntegral_const _ _
  have hcount : (∑' n, planarBrownianMotion x (A n)) ≤
      ∫⁻ b, (τ b + 1) ∂(planarBrownianMotion x) := by
    have heq : (∑' n, planarBrownianMotion x (A n)) =
        ∫⁻ b, ∑' n : ℕ, {e' : ℝ≥0∞ | ((n : ℝ≥0) : ℝ≥0∞) < e'}.indicator
          (fun _ => (1 : ℝ≥0∞)) (τ b) ∂(planarBrownianMotion x) := by
      have hmeas (n : ℕ) : AEMeasurable (fun b => {e' : ℝ≥0∞ | ((n : ℝ≥0) : ℝ≥0∞) < e'}.indicator
          (fun _ => (1 : ℝ≥0∞)) (τ b)) (planarBrownianMotion x) :=
        ((measurable_const.indicator (measurableSet_lt measurable_const measurable_id)).comp
          hτm).aemeasurable
      rw [lintegral_tsum hmeas]
      congr 1
      funext n
      rw [← lintegral_indicator_one (hAm n)]
      congr 1
    rw [heq]
    exact lintegral_mono (fun b => tsum_indicator_natCast_lt_le (τ b))
  calc
    _ ≤ ∫⁻ p, ∑' n, term n p ∂(P.prod (planarBrownianMotion x)) := lintegral_mono_ae hpoint
    _ = ∑' n, ∫⁻ p, term n p ∂(P.prod (planarBrownianMotion x)) :=
      lintegral_tsum (fun n => (htermm n).aemeasurable)
    _ ≤ ∑' n, c * planarBrownianMotion x (A n) := ENNReal.tsum_le_tsum hn
    _ = c * ∑' n, planarBrownianMotion x (A n) := ENNReal.tsum_mul_left
    _ ≤ c * ∫⁻ b, (τ b + 1) ∂(planarBrownianMotion x) := mul_le_mul_of_nonneg_left hcount zero_le

end HarmonicBalls
