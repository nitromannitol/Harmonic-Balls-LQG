import HarmonicBalls.Proofs.Potential.ReflectedNeumannMixing
import HarmonicBalls.Proofs.Potential.HeatKernelL2Operator

/-!
# The centered Green kernel of the Neumann kernel of the square

For `x ≠ y` in `K₀ = [0, 1]²` put `g(x, y) = ∫_0^∞ (k_s(x, y) - 1) ds`
(`centeredGreenKernel`), the Green kernel of reflected Brownian motion in `K₀` centered with
respect to Lebesgue measure. By the bound `k_s(x, y) ≤ C s^{θ-1} |x - y|^{-2θ}` for `s ≤ 1`
(`exists_neumannKernel_le_rpow`) and the exponential mixing `|k_s - 1| ≤ C e^{-cs}` for `s ≥ 1`,
the integrand is dominated by `a(s) |x - y|^{-2θ} + b(s)` with `a, b` integrable on `(0, ∞)`
(`exists_neumannKernel_majorant`), so `|g(x, y)| ≤ C₁ |x - y|^{-2θ} + C₂`.

For `ε ∈ (0, 1]`, `g = g_ε + h_ε` off the diagonal (`centeredGreenKernel_eq`), where the tail
`g_ε(x, y) = ∫_ε^∞ (k_s(x, y) - 1) ds - ε` is jointly continuous on `K₀ × K₀`
(`continuousOn_greenKernelTail`) and the head `h_ε(x, y) = ∫_0^ε k_s(x, y) ds` is at most
`C ε^θ |x - y|^{-2θ} / θ` (`greenKernelHead_le`).

Let `ν` be a probability measure carried by `K₀` with upper bounds `ν(B̄(y, r)) ≤ A r^β` for
`y ∈ K₀`. With `4θ < β`, the Riesz potential `∫ |x - y|^{-4θ} ν(dy)` is bounded on `K₀`
(`lintegral_norm_sub_rpow_neg_le`), so each row `g(x, ·)` is in `L²(ν)` with a uniform bound
(`greenRow`, `norm_greenRow_le`), the heads are uniformly small in `L²(ν)`, and the rows depend
continuously on `x ∈ K₀` in `L²(ν)` (`continuousOn_greenRow`): they are uniform limits of the
rows of the continuous kernels `g_ε`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal InnerProductSpace

namespace HarmonicBalls

/-! ### Bounds for the Neumann kernel off the diagonal -/

/-- **Off-diagonal bound** for `0 < s ≤ 1`: `k_s(x, y) ≤ C s^{θ-1} |x - y|^{-2θ}`. -/
theorem exists_neumannKernel_le_rpow {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ closedSquare (0 : ℂ) 1, ∀ y ∈ closedSquare (0 : ℂ) 1, x ≠ y →
      ∀ s ∈ Ioc (0 : ℝ) 1, neumannKernel s x y ≤ C * s ^ (θ - 1) * ‖x - y‖ ^ (-(2 * θ)) := by
  set T : ℝ≥0∞ := (2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum) ^ 2 with hT
  have hTne : T ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
    ENNReal.ofReal_ne_top) foldLatticeSum_lt_top.ne)
  refine ⟨T.toReal * ((2 * Real.pi)⁻¹ * 2 ^ θ), by positivity, fun x hx y hy hxy s hs => ?_⟩
  have h := squareNeumannKernel_le_rpow hx hy (Ne.symm hxy) hθ0 hθ1 hs
  have hs0 : 0 ≤ s ^ (θ - 1) := Real.rpow_nonneg hs.1.le _
  have ha : 0 ≤ (2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1) := mul_nonneg (by positivity) hs0
  have hw : 0 ≤ ‖x - y‖ ^ (-(2 * θ)) := by positivity
  have hR : T * ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1)) *
      ENNReal.ofReal (‖x - y‖ ^ (-(2 * θ))) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hTne ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have h' := ENNReal.toReal_mono hR h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal hw] at h'
  unfold neumannKernel
  exact h'.trans_eq (by ring)

/-- **An integrable majorant**: `|k_s(x, y) - 1| ≤ a(s) |x - y|^{-2θ} + b(s)` for `s > 0` and
`x ≠ y` in `K₀`, with `a, b ≥ 0` integrable on `(0, ∞)`. -/
theorem exists_neumannKernel_majorant {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ a b : ℝ → ℝ, Measurable a ∧ Measurable b ∧ IntegrableOn a (Ioi 0) ∧
      IntegrableOn b (Ioi 0) ∧ (∀ s, 0 ≤ a s) ∧ (∀ s, 0 ≤ b s) ∧
      ∀ x ∈ closedSquare (0 : ℂ) 1, ∀ y ∈ closedSquare (0 : ℂ) 1, x ≠ y → ∀ s : ℝ, 0 < s →
        |neumannKernel s x y - 1| ≤ a s * ‖x - y‖ ^ (-(2 * θ)) + b s := by
  obtain ⟨C, hC0, hC⟩ := exists_neumannKernel_le_rpow hθ0 hθ1
  obtain ⟨D, c, hD0, hc, hD⟩ := exists_abs_neumannKernel_sub_one_le
  refine ⟨(Ioc (0 : ℝ) 1).indicator fun s => C * s ^ (θ - 1),
    fun s => (Ioc (0 : ℝ) 1).indicator 1 s + D * Real.exp (-c * s), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (measurable_const.mul (measurable_id.pow_const _)).indicator measurableSet_Ioc
  · exact (measurable_one.indicator measurableSet_Ioc).add
      (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_id.const_mul _)))
  · have hi : IntegrableOn (fun s : ℝ => C * s ^ (θ - 1)) (Ioc (0 : ℝ) 1) := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (by linarith : -1 < θ - 1)).1
      exact h.const_mul C
    exact ((integrable_indicator_iff measurableSet_Ioc).2 hi).integrableOn
  · have h1 : IntegrableOn ((Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ)) (Ioi 0) :=
      ((integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const
        (by simp) )).integrableOn
    exact h1.add ((exp_neg_integrableOn_Ioi 0 hc).const_mul D)
  · intro s
    by_cases hs : s ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hs]
      exact mul_nonneg hC0 (Real.rpow_nonneg hs.1.le _)
    · rw [indicator_of_notMem hs]
  · intro s
    exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (mul_nonneg hD0 (Real.exp_pos _).le)
  · intro x hx y hy hxy s hs
    beta_reduce
    have hw : 0 ≤ ‖x - y‖ ^ (-(2 * θ)) := by positivity
    have he : 0 ≤ D * Real.exp (-c * s) := mul_nonneg hD0 (Real.exp_pos _).le
    by_cases hs1 : s ≤ 1
    · have hsI : s ∈ Ioc (0 : ℝ) 1 := ⟨hs, hs1⟩
      rw [indicator_of_mem hsI, indicator_of_mem hsI, Pi.one_apply]
      have h1 := hC x hx y hy hxy s hsI
      have h2 := neumannKernel_nonneg s x y
      have h3 : 0 ≤ C * s ^ (θ - 1) * ‖x - y‖ ^ (-(2 * θ)) :=
        mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hs.le _)) hw
      rw [abs_le]
      constructor <;> nlinarith
    · have hsI : s ∉ Ioc (0 : ℝ) 1 := fun h => hs1 h.2
      rw [indicator_of_notMem hsI, indicator_of_notMem hsI, zero_mul, zero_add, zero_add]
      have h := hD s (le_of_not_ge hs1) x hx y hy
      rw [neg_mul]
      exact h

/-! ### The centered Green kernel -/

theorem measurable_neumannKernel_time (x y : ℂ) : Measurable fun s => neumannKernel s x y :=
  measurable_neumannKernel_uncurry.comp (f := fun s : ℝ => (s, x, y)) (by fun_prop)

/-- The centered Green kernel `g(x, y) = ∫_0^∞ (k_s(x, y) - 1) ds`. -/
noncomputable def centeredGreenKernel (x y : ℂ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), (neumannKernel s x y - 1)

/-- The head `h_ε(x, y) = ∫_0^ε k_s(x, y) ds`. -/
noncomputable def greenKernelHead (ε : ℝ) (x y : ℂ) : ℝ :=
  ∫ s in Ioc (0 : ℝ) ε, neumannKernel s x y

/-- The tail `g_ε(x, y) = ∫_ε^∞ (k_s(x, y) - 1) ds - ε`. -/
noncomputable def greenKernelTail (ε : ℝ) (x y : ℂ) : ℝ :=
  (∫ s in Ioi ε, (neumannKernel s x y - 1)) - ε

theorem measurable_centeredGreenKernel_uncurry :
    Measurable fun p : ℂ × ℂ => centeredGreenKernel p.1 p.2 := by
  have hf : StronglyMeasurable fun q : (ℂ × ℂ) × ℝ => neumannKernel q.2 q.1.1 q.1.2 - 1 :=
    ((measurable_neumannKernel_uncurry.comp (measurable_snd.prodMk
      (measurable_fst.fst.prodMk measurable_fst.snd))).sub measurable_const).stronglyMeasurable
  exact (hf.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

theorem measurable_centeredGreenKernel (x : ℂ) : Measurable (centeredGreenKernel x) :=
  measurable_centeredGreenKernel_uncurry.comp (measurable_const.prodMk measurable_id)

theorem centeredGreenKernel_comm (x y : ℂ) : centeredGreenKernel x y = centeredGreenKernel y x := by
  unfold centeredGreenKernel
  simp_rw [neumannKernel_comm _ x y]

/-- **Integrability and the bound of the centered Green kernel** off the diagonal. -/
theorem exists_abs_centeredGreenKernel_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ x ∈ closedSquare (0 : ℂ) 1, ∀ y ∈ closedSquare (0 : ℂ) 1,
      x ≠ y → IntegrableOn (fun s => neumannKernel s x y - 1) (Ioi 0) ∧
        |centeredGreenKernel x y| ≤ C₁ * ‖x - y‖ ^ (-(2 * θ)) + C₂ := by
  obtain ⟨a, b, ham, hbm, hai, hbi, ha0, hb0, hab⟩ := exists_neumannKernel_majorant hθ0 hθ1
  refine ⟨∫ s in Ioi (0 : ℝ), a s, ∫ s in Ioi (0 : ℝ), b s, setIntegral_nonneg measurableSet_Ioi
    fun s _ => ha0 s, setIntegral_nonneg measurableSet_Ioi fun s _ => hb0 s,
    fun x hx y hy hxy => ?_⟩
  have hmaj : IntegrableOn (fun s => a s * ‖x - y‖ ^ (-(2 * θ)) + b s) (Ioi 0) :=
    (hai.mul_const _).add hbi
  have hle : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      ‖neumannKernel s x y - 1‖ ≤ a s * ‖x - y‖ ^ (-(2 * θ)) + b s :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => by
      rw [Real.norm_eq_abs]; exact hab x hx y hy hxy s hs)
  have hmeas : AEStronglyMeasurable (fun s => neumannKernel s x y - 1)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_neumannKernel_time x y).sub measurable_const).aestronglyMeasurable
  refine ⟨hmaj.mono' hmeas hle, ?_⟩
  have h := norm_integral_le_of_norm_le hmaj hle
  rw [integral_add (hai.mul_const _) hbi, integral_mul_const, Real.norm_eq_abs] at h
  exact h

theorem integrableOn_neumannKernel_sub_one {x y : ℂ} (hx : x ∈ closedSquare 0 1)
    (hy : y ∈ closedSquare 0 1) (hxy : x ≠ y) :
    IntegrableOn (fun s => neumannKernel s x y - 1) (Ioi 0) := by
  obtain ⟨C₁, C₂, -, -, h⟩ := exists_abs_centeredGreenKernel_le one_pos le_rfl
  exact (h x hx y hy hxy).1

/-- `g = g_ε + h_ε` off the diagonal. -/
theorem centeredGreenKernel_eq {ε : ℝ} (hε : 0 < ε) {x y : ℂ} (hx : x ∈ closedSquare 0 1)
    (hy : y ∈ closedSquare 0 1) (hxy : x ≠ y) :
    centeredGreenKernel x y = greenKernelTail ε x y + greenKernelHead ε x y := by
  have hi := integrableOn_neumannKernel_sub_one hx hy hxy
  have h1 : IntegrableOn (fun s => neumannKernel s x y - 1) (Ioc 0 ε) :=
    hi.mono_set Ioc_subset_Ioi_self
  have h2 : IntegrableOn (fun s => neumannKernel s x y - 1) (Ioi ε) :=
    hi.mono_set (Ioi_subset_Ioi hε.le)
  have hk : IntegrableOn (fun s => neumannKernel s x y) (Ioc 0 ε) := by
    have := h1.add (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) ε) (C := (1 : ℝ))
      (by simp))
    exact this.congr_fun (fun s _ => by simp) measurableSet_Ioc
  have hconst : ∫ _ in Ioc (0 : ℝ) ε, (1 : ℝ) = ε := by
    rw [← intervalIntegral.integral_of_le hε.le, intervalIntegral.integral_const, smul_eq_mul,
      mul_one, sub_zero]
  unfold centeredGreenKernel greenKernelTail greenKernelHead
  rw [← Ioc_union_Ioi_eq_Ioi hε.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    h1 h2, integral_sub hk (integrableOn_const (by simp)), hconst]
  ring

/-- **The tail is continuous** on `K₀ × K₀` for `ε > 0`. -/
theorem continuousOn_greenKernelTail {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun p : ℂ × ℂ => greenKernelTail ε p.1 p.2)
      (closedSquare 0 1 ×ˢ closedSquare 0 1) := by
  obtain ⟨D, c, hD0, hc, hD⟩ := exists_abs_neumannKernel_sub_one_le
  obtain ⟨Cε, hCε0, hCε⟩ := exists_neumannKernel_le hε (show ε ≤ max ε 1 from le_max_left _ _)
  set D' := max ((Cε + 1) * Real.exp c) D with hD'
  have hbound : ∀ p ∈ closedSquare (0 : ℂ) 1 ×ˢ closedSquare (0 : ℂ) 1, ∀ s, ε < s →
      ‖neumannKernel s p.1 p.2 - 1‖ ≤ D' * Real.exp (-c * s) := by
    rintro p ⟨hp1, hp2⟩ s hs
    rw [Real.norm_eq_abs]
    by_cases hs1 : s ≤ 1
    · have h1 := hCε s ⟨hs.le, hs1.trans (le_max_right _ _)⟩ p.1 hp1 p.2 hp2
      have h2 := neumannKernel_nonneg s p.1 p.2
      have h3 : 1 ≤ Real.exp c * Real.exp (-c * s) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      have h4 : |neumannKernel s p.1 p.2 - 1| ≤ Cε + 1 := by
        rw [abs_le]; constructor <;> linarith
      calc |neumannKernel s p.1 p.2 - 1| ≤ (Cε + 1) * 1 := by linarith
        _ ≤ (Cε + 1) * (Real.exp c * Real.exp (-c * s)) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
        _ = (Cε + 1) * Real.exp c * Real.exp (-c * s) := by ring
        _ ≤ D' * Real.exp (-c * s) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · have h := hD s (le_of_not_ge hs1) p.1 hp1 p.2 hp2
      rw [neg_mul] at ⊢
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  have hcont : ContinuousOn (fun p : ℂ × ℂ => ∫ s in Ioi ε, (neumannKernel s p.1 p.2 - 1))
      (closedSquare 0 1 ×ˢ closedSquare 0 1) := by
    refine continuousOn_of_dominated (bound := fun s => D' * Real.exp (-c * s))
      (fun p _ => ((measurable_neumannKernel_time p.1 p.2).sub
        measurable_const).aestronglyMeasurable) (fun p hp => ?_)
      ((exp_neg_integrableOn_Ioi ε hc).const_mul D') ?_
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs =>
        hbound p hp s hs)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
      have hs0 : 0 < s := hε.trans hs
      exact ((continuousOn_neumannKernel hs0 le_rfl).comp
        (f := fun p : ℂ × ℂ => (s, p.1, p.2)) (Continuous.continuousOn (by fun_prop))
        fun p hp => ⟨⟨le_rfl, le_rfl⟩, hp.1, hp.2⟩).sub continuousOn_const
  exact hcont.sub continuousOn_const

/-- **The head is small**: `0 ≤ h_ε(x, y) ≤ C ε^θ |x - y|^{-2θ} / θ` for `0 < ε ≤ 1`. -/
theorem greenKernelHead_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x ∈ closedSquare (0 : ℂ) 1,
      ∀ y ∈ closedSquare (0 : ℂ) 1, x ≠ y → 0 ≤ greenKernelHead ε x y ∧
        greenKernelHead ε x y ≤ C * ε ^ θ * ‖x - y‖ ^ (-(2 * θ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_neumannKernel_le_rpow hθ0 hθ1
  refine ⟨C / θ, div_nonneg hC0 hθ0.le, fun ε hε hε1 x hx y hy hxy => ⟨?_, ?_⟩⟩
  · exact setIntegral_nonneg measurableSet_Ioc fun s _ => neumannKernel_nonneg _ _ _
  · have hrp : IntegrableOn (fun s : ℝ => s ^ (θ - 1)) (Ioc 0 ε) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ε) (by linarith : -1 < θ - 1)).1
    have hmaj : IntegrableOn (fun s => C * s ^ (θ - 1) * ‖x - y‖ ^ (-(2 * θ))) (Ioc 0 ε) :=
      (hrp.const_mul C).mul_const _
    have hk : IntegrableOn (fun s => neumannKernel s x y) (Ioc 0 ε) := by
      refine hmaj.mono' (measurable_neumannKernel_time x y).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall fun s hs => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (neumannKernel_nonneg _ _ _)]
      exact hC x hx y hy hxy s ⟨hs.1, hs.2.trans hε1⟩
    have hle := setIntegral_mono_on hk hmaj measurableSet_Ioc fun s hs =>
      hC x hx y hy hxy s ⟨hs.1, hs.2.trans hε1⟩
    have hval : ∫ s in Ioc (0 : ℝ) ε, s ^ (θ - 1) = ε ^ θ / θ := by
      rw [← intervalIntegral.integral_of_le hε.le, integral_rpow (Or.inl (by linarith))]
      rw [show θ - 1 + 1 = θ by ring, Real.zero_rpow hθ0.ne', sub_zero]
    unfold greenKernelHead
    refine hle.trans (le_of_eq ?_)
    rw [integral_mul_const, integral_const_mul, hval]
    ring

/-! ### Rows of the kernel in `L²(ν)` -/

section Rows

variable {ν : Measure ℂ}

/-- The row `g(x, ·)` as an element of `L²(ν)` (zero if the row is not square integrable). -/
noncomputable def greenRow (ν : Measure ℂ) (x : ℂ) : Lp ℝ 2 ν :=
  open Classical in
  if h : MemLp (centeredGreenKernel x) 2 ν then h.toLp _ else 0

theorem greenRow_eq {x : ℂ} (h : MemLp (centeredGreenKernel x) 2 ν) :
    greenRow ν x = h.toLp _ := by
  unfold greenRow
  simp [h]

/-- `(‖v‖^{-2θ})² = ‖v‖^{-4θ}`. -/
theorem rpow_neg_two_mul_sq (v : ℂ) (θ : ℝ) :
    (‖v‖ ^ (-(2 * θ))) ^ 2 = ‖v‖ ^ (-(4 * θ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

/-- The standing hypotheses on `ν` for the rows: `ν` is carried by `K₀`, and
`ν(B̄(y, r)) ≤ A r^β` for `y ∈ K₀` and `r > 0`. -/
structure IsUpperRegularSpeed (ν : Measure ℂ) : Prop where
  carried : ν (closedSquare 0 1)ᶜ = 0
  bound : ∃ A β : ℝ, 0 ≤ A ∧ 0 < β ∧ ∀ y ∈ closedSquare (0 : ℂ) 1, ∀ r : ℝ, 0 < r →
    ν (closedBall y r) ≤ ENNReal.ofReal (A * r ^ β)

theorem IsUpperRegularSpeed.ae_mem (hν : IsUpperRegularSpeed ν) :
    ∀ᵐ y ∂ν, y ∈ closedSquare (0 : ℂ) 1 := by
  rw [ae_iff]
  exact hν.carried

theorem IsUpperRegularSpeed.singleton_eq_zero (hν : IsUpperRegularSpeed ν) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) : ν {x} = 0 := by
  obtain ⟨A, β, hA, hβ, hb⟩ := hν.bound
  have hlim : Tendsto (fun r : ℝ => A * r ^ β) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuous_rpow_const hβ.le).tendsto 0).const_mul A
    rw [Real.zero_rpow hβ.ne', mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim' : Tendsto (fun r : ℝ => ENNReal.ofReal (A * r ^ β)) (𝓝[>] 0) (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto _).comp hlim
    rwa [ENNReal.ofReal_zero] at h
  refine le_antisymm (ge_of_tendsto hlim' ?_) zero_le
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (measure_mono (singleton_subset_iff.2 (mem_closedBall_self (le_of_lt hr)))).trans
    (hb x hx r hr)

theorem IsUpperRegularSpeed.ae_ne (hν : IsUpperRegularSpeed ν) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) : ∀ᵐ y ∂ν, y ≠ x := by
  rw [ae_iff]
  simpa using hν.singleton_eq_zero hx

/-- **The Riesz potential bound**: for `0 < α < β`, `∫ |x - y|^{-α} ν(dy)` is bounded on `K₀`. -/
theorem IsUpperRegularSpeed.exists_riesz_le [IsProbabilityMeasure ν] (hν : IsUpperRegularSpeed ν) :
    ∃ β : ℝ, 0 < β ∧ ∀ α : ℝ, 0 < α → α < β → ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ closedSquare (0 : ℂ) 1,
      ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-α)) ∂ν ≤ ENNReal.ofReal R := by
  obtain ⟨A, β, hA, hβ, hb⟩ := hν.bound
  refine ⟨β, hβ, fun α hα hαβ => ⟨1 + A * (α / (β - α)), by
    have : 0 ≤ α / (β - α) := div_nonneg hα.le (by linarith)
    positivity, fun x hx => ?_⟩⟩
  exact lintegral_norm_sub_rpow_neg_le hα hαβ zero_le_one hA (by simp) (hb x hx)

/-- The exponent `θ = min 1 (β/8)` with `4θ < β`. -/
theorem exists_theta {β : ℝ} (hβ : 0 < β) : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 4 * θ < β :=
  ⟨min 1 (β / 8), lt_min one_pos (by positivity), min_le_left _ _,
    by have := min_le_right 1 (β / 8); linarith⟩

theorem integrable_rpow_neg_of_lintegral {x : ℂ} {α R : ℝ}
    (h : ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-α)) ∂ν ≤ ENNReal.ofReal R) :
    Integrable (fun y => ‖x - y‖ ^ (-α)) ν := by
  refine (lintegral_ofReal_ne_top_iff_integrable
    (by fun_prop : Measurable fun y : ℂ => ‖x - y‖ ^ (-α)).aestronglyMeasurable
    (Eventually.of_forall fun y => by positivity)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)

theorem integral_rpow_neg_le_of_lintegral {x : ℂ} {α R : ℝ} (hR : 0 ≤ R)
    (h : ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-α)) ∂ν ≤ ENNReal.ofReal R) :
    ∫ y, ‖x - y‖ ^ (-α) ∂ν ≤ R := by
  have hi := integrable_rpow_neg_of_lintegral h
  rw [← ENNReal.ofReal_le_ofReal_iff hR, ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun y => by positivity)]
  exact h

/-- **Square integrability of the rows, with a uniform bound.** -/
theorem IsUpperRegularSpeed.exists_memLp_centeredGreenKernel [IsProbabilityMeasure ν] (hν : IsUpperRegularSpeed ν) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ closedSquare (0 : ℂ) 1, MemLp (centeredGreenKernel x) 2 ν ∧
      ∫ y, centeredGreenKernel x y ^ 2 ∂ν ≤ B := by
  obtain ⟨β, hβ, hR⟩ := hν.exists_riesz_le
  obtain ⟨θ, hθ0, hθ1, hθβ⟩ := exists_theta hβ
  obtain ⟨R, hR0, hRx⟩ := hR (4 * θ) (by positivity) hθβ
  obtain ⟨C₁, C₂, hC₁, hC₂, hg⟩ := exists_abs_centeredGreenKernel_le hθ0 hθ1
  refine ⟨2 * (C₁ ^ 2 * R + C₂ ^ 2), by positivity, fun x hx => ?_⟩
  have hw := integrable_rpow_neg_of_lintegral (hRx x hx)
  have hmaj : Integrable (fun y => 2 * (C₁ ^ 2 * ‖x - y‖ ^ (-(4 * θ)) + C₂ ^ 2)) ν :=
    ((hw.const_mul _).add (integrable_const _)).const_mul _
  have hle : ∀ᵐ y ∂ν, ‖centeredGreenKernel x y ^ 2‖ ≤
      2 * (C₁ ^ 2 * ‖x - y‖ ^ (-(4 * θ)) + C₂ ^ 2) := by
    filter_upwards [hν.ae_mem, hν.ae_ne hx] with y hy hyx
    have h := (hg x hx y hy (Ne.symm hyx)).2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← rpow_neg_two_mul_sq]
    have hw0 : 0 ≤ ‖x - y‖ ^ (-(2 * θ)) := by positivity
    have : centeredGreenKernel x y ^ 2 ≤ (C₁ * ‖x - y‖ ^ (-(2 * θ)) + C₂) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    nlinarith [sq_nonneg (C₁ * ‖x - y‖ ^ (-(2 * θ)) - C₂)]
  have hsq : Integrable (fun y => centeredGreenKernel x y ^ 2) ν :=
    hmaj.mono' ((measurable_centeredGreenKernel x).pow_const 2).aestronglyMeasurable hle
  refine ⟨(memLp_two_iff_integrable_sq (measurable_centeredGreenKernel x).aestronglyMeasurable).2 hsq,
    ?_⟩
  calc ∫ y, centeredGreenKernel x y ^ 2 ∂ν ≤ ∫ y, 2 * (C₁ ^ 2 * ‖x - y‖ ^ (-(4 * θ)) + C₂ ^ 2) ∂ν :=
        integral_mono_ae hsq hmaj (hle.mono fun y h => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h; exact h)
    _ = 2 * (C₁ ^ 2 * ∫ y, ‖x - y‖ ^ (-(4 * θ)) ∂ν + C₂ ^ 2) := by
        rw [integral_const_mul, integral_add (hw.const_mul _) (integrable_const _), integral_const_mul,
          integral_const, smul_eq_mul, probReal_univ, one_mul]
    _ ≤ 2 * (C₁ ^ 2 * R + C₂ ^ 2) := by
        have := integral_rpow_neg_le_of_lintegral hR0 (hRx x hx)
        have hC : 0 ≤ C₁ ^ 2 := sq_nonneg _
        nlinarith

theorem norm_sq_toLp_eq {f : ℂ → ℝ} (hf : MemLp f 2 ν) :
    ‖hf.toLp f‖ ^ 2 = ∫ y, f y ^ 2 ∂ν := by
  rw [l2_norm_sq_eq_integral_sq]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with y hy
  rw [hy]

theorem norm_le_of_norm_sq_le {u : Lp ℝ 2 ν} {η : ℝ} (hη : 0 ≤ η) (h : ‖u‖ ^ 2 ≤ η ^ 2) :
    ‖u‖ ≤ η :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) hη (by norm_num : (2 : ℕ) ≠ 0)).1 h

/-- **The rows are uniformly bounded in `L²(ν)`.** -/
theorem IsUpperRegularSpeed.exists_norm_greenRow_le [IsProbabilityMeasure ν] (hν : IsUpperRegularSpeed ν) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ closedSquare (0 : ℂ) 1, ‖greenRow ν x‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := hν.exists_memLp_centeredGreenKernel
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, fun x hx => ?_⟩
  obtain ⟨hm, hle⟩ := hB x hx
  refine norm_le_of_norm_sq_le (Real.sqrt_nonneg _) ?_
  rw [greenRow_eq hm, norm_sq_toLp_eq hm, Real.sq_sqrt hB0]
  exact hle

theorem IsUpperRegularSpeed.coeFn_greenRow [IsProbabilityMeasure ν] (hν : IsUpperRegularSpeed ν) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) :
    (greenRow ν x : ℂ → ℝ) =ᵐ[ν] centeredGreenKernel x := by
  obtain ⟨B, -, hB⟩ := hν.exists_memLp_centeredGreenKernel
  rw [greenRow_eq (hB x hx).1]
  exact (hB x hx).1.coeFn_toLp

/-- **The rows depend continuously on `x ∈ K₀` in `L²(ν)`.** -/
theorem IsUpperRegularSpeed.continuousOn_greenRow [IsProbabilityMeasure ν] (hν : IsUpperRegularSpeed ν) :
    ContinuousOn (greenRow ν) (closedSquare 0 1) := by
  obtain ⟨β, hβ, hR⟩ := hν.exists_riesz_le
  obtain ⟨θ, hθ0, hθ1, hθβ⟩ := exists_theta hβ
  obtain ⟨R, hR0, hRx⟩ := hR (4 * θ) (by positivity) hθβ
  obtain ⟨C, hC0, hC⟩ := greenKernelHead_le hθ0 hθ1
  obtain ⟨B, -, hB⟩ := hν.exists_memLp_centeredGreenKernel
  -- the heads in `L²(ν)`
  have hhead : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x ∈ closedSquare (0 : ℂ) 1,
      MemLp (greenKernelHead ε x) 2 ν ∧
        ∫ y, greenKernelHead ε x y ^ 2 ∂ν ≤ (C * ε ^ θ) ^ 2 * R := by
    intro ε hε hε1 x hx
    have hw := integrable_rpow_neg_of_lintegral (hRx x hx)
    have hmeas : Measurable (greenKernelHead ε x) := by
      have hf : StronglyMeasurable fun q : ℂ × ℝ => neumannKernel q.2 x q.1 :=
        (measurable_neumannKernel_uncurry.comp (measurable_snd.prodMk
          (measurable_const.prodMk measurable_fst))).stronglyMeasurable
      exact (hf.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) ε))).measurable
    have hle : ∀ᵐ y ∂ν, ‖greenKernelHead ε x y ^ 2‖ ≤ (C * ε ^ θ) ^ 2 * ‖x - y‖ ^ (-(4 * θ)) := by
      filter_upwards [hν.ae_mem, hν.ae_ne hx] with y hy hyx
      obtain ⟨h0, h1⟩ := hC ε hε hε1 x hx y hy (Ne.symm hyx)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← rpow_neg_two_mul_sq, ← mul_pow]
      exact pow_le_pow_left₀ h0 (h1.trans_eq (by ring)) 2
    have hsq : Integrable (fun y => greenKernelHead ε x y ^ 2) ν :=
      (hw.const_mul _).mono' (hmeas.pow_const 2).aestronglyMeasurable hle
    refine ⟨(memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hsq, ?_⟩
    calc ∫ y, greenKernelHead ε x y ^ 2 ∂ν ≤ ∫ y, (C * ε ^ θ) ^ 2 * ‖x - y‖ ^ (-(4 * θ)) ∂ν :=
          integral_mono_ae hsq (hw.const_mul _) (hle.mono fun y h => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h; exact h)
      _ = (C * ε ^ θ) ^ 2 * ∫ y, ‖x - y‖ ^ (-(4 * θ)) ∂ν := integral_const_mul _ _
      _ ≤ (C * ε ^ θ) ^ 2 * R := mul_le_mul_of_nonneg_left
          (integral_rpow_neg_le_of_lintegral hR0 (hRx x hx)) (sq_nonneg _)
  -- the tails are bounded and continuous on `K₀ × K₀`
  have htail : ∀ ε : ℝ, 0 < ε → ∀ x ∈ closedSquare (0 : ℂ) 1, MemLp (greenKernelTail ε x) 2 ν := by
    intro ε hε x hx
    obtain ⟨M, hM⟩ := (isCompact_closedSquare (0 : ℂ) 1).exists_bound_of_continuousOn
      ((continuousOn_greenKernelTail hε).comp (f := fun y : ℂ => (x, y))
        (Continuous.continuousOn (by fun_prop)) fun y hy => ⟨hx, hy⟩)
    have hmeas : Measurable (greenKernelTail ε x) := by
      have hf : StronglyMeasurable fun q : ℂ × ℝ => neumannKernel q.2 x q.1 - 1 :=
        ((measurable_neumannKernel_uncurry.comp (measurable_snd.prodMk
          (measurable_const.prodMk measurable_fst))).sub measurable_const).stronglyMeasurable
      exact (hf.integral_prod_right' (ν := volume.restrict (Ioi ε))).measurable.sub_const _
    refine memLp_of_bounded (μ := ν) (a := -M) (b := M) ?_ hmeas.aestronglyMeasurable 2
    filter_upwards [hν.ae_mem] with y hy
    have := hM y hy
    rw [Real.norm_eq_abs] at this
    exact abs_le.1 this
  rw [Metric.continuousOn_iff]
  intro x hx η hη
  -- choose `ε` with the heads small
  have hlim : Tendsto (fun ε : ℝ => C * ε ^ θ) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuous_rpow_const hθ0.le).tendsto 0).const_mul C
    rw [Real.zero_rpow hθ0.ne', mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C * ε ^ θ * Real.sqrt R < η / 3 := by
    have h := hlim.mul_const (Real.sqrt R)
    rw [zero_mul] at h
    exact h.eventually (gt_mem_nhds (by linarith))
  obtain ⟨ε, ⟨hεs, hε1⟩, hε0⟩ := ((hsmall.and (Ioo_mem_nhdsGT one_pos)).and
    self_mem_nhdsWithin).exists
  have hε0' : 0 < ε := hε0
  have hε1' : ε ≤ 1 := hε1.2.le
  -- uniform continuity of the tail
  have huc := (isCompact_closedSquare (0 : ℂ) 1).prod (isCompact_closedSquare (0 : ℂ) 1)
    |>.uniformContinuousOn_of_continuous (continuousOn_greenKernelTail hε0')
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨ρ, hρ, hρu⟩ := huc (η / 3) (by linarith)
  refine ⟨ρ, hρ, fun x' hx' hxx' => ?_⟩
  -- decompose the rows
  have hdec : ∀ z (hz : z ∈ closedSquare (0 : ℂ) 1), greenRow ν z =
      (htail ε hε0' z hz).toLp _ + (hhead ε hε0' hε1' z hz).1.toLp _ := by
    intro z hz
    rw [greenRow_eq (hB z hz).1, ← MemLp.toLp_add]
    refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
    filter_upwards [hν.ae_mem, hν.ae_ne hz] with y hy hyz
    rw [Pi.add_apply, centeredGreenKernel_eq hε0' hz hy (Ne.symm hyz)]
  rw [dist_eq_norm, hdec x' hx', hdec x hx]
  have hn1 : ‖(htail ε hε0' x' hx').toLp (greenKernelTail ε x') -
      (htail ε hε0' x hx).toLp (greenKernelTail ε x)‖ ≤ η / 3 := by
    rw [← MemLp.toLp_sub]
    refine norm_le_of_norm_sq_le (by linarith) ?_
    rw [norm_sq_toLp_eq]
    calc ∫ y, (greenKernelTail ε x' - greenKernelTail ε x) y ^ 2 ∂ν ≤ ∫ _, (η / 3) ^ 2 ∂ν := by
          refine integral_mono_ae ((htail ε hε0' x' hx').sub (htail ε hε0' x hx)).integrable_sq
            (integrable_const _) ?_
          filter_upwards [hν.ae_mem] with y hy
          have h := hρu (x', y) ⟨hx', hy⟩ (x, y) ⟨hx, hy⟩ (by
            rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hxx')
          rw [Real.dist_eq] at h
          rw [Pi.sub_apply, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h.le 2
      _ = (η / 3) ^ 2 := by simp
  have hn2 : ∀ z (hz : z ∈ closedSquare (0 : ℂ) 1),
      ‖(hhead ε hε0' hε1' z hz).1.toLp (greenKernelHead ε z)‖ < η / 3 := by
    intro z hz
    have hpos : 0 ≤ C * ε ^ θ * Real.sqrt R :=
      mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hε0'.le _)) (Real.sqrt_nonneg _)
    refine (norm_le_of_norm_sq_le hpos ?_).trans_lt hεs
    rw [norm_sq_toLp_eq, mul_pow, Real.sq_sqrt hR0]
    exact (hhead ε hε0' hε1' z hz).2
  calc ‖(htail ε hε0' x' hx').toLp (greenKernelTail ε x') +
        (hhead ε hε0' hε1' x' hx').1.toLp (greenKernelHead ε x') -
        ((htail ε hε0' x hx).toLp (greenKernelTail ε x) +
        (hhead ε hε0' hε1' x hx).1.toLp (greenKernelHead ε x))‖
      = ‖((htail ε hε0' x' hx').toLp (greenKernelTail ε x') -
          (htail ε hε0' x hx).toLp (greenKernelTail ε x)) +
        (hhead ε hε0' hε1' x' hx').1.toLp (greenKernelHead ε x') -
        (hhead ε hε0' hε1' x hx).1.toLp (greenKernelHead ε x)‖ := by congr 1; abel
    _ ≤ ‖(htail ε hε0' x' hx').toLp (greenKernelTail ε x') -
          (htail ε hε0' x hx).toLp (greenKernelTail ε x)‖ +
        ‖(hhead ε hε0' hε1' x' hx').1.toLp (greenKernelHead ε x')‖ +
        ‖(hhead ε hε0' hε1' x hx).1.toLp (greenKernelHead ε x)‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ < η := by linarith [hn1, hn2 x' hx', hn2 x hx]

end Rows

end HarmonicBalls
