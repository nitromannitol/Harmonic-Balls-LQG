import HarmonicBalls.Proofs.Potential.ReflectedGreenOperator
import HarmonicBalls.Proofs.Potential.ReflectedHeatKernelChapmanKolmogorov

/-!
# Positivity and injectivity of the centered Green operator on the functions of mean zero

Let `ν` be a probability measure carried by `K₀` with upper power bounds and `f ∈ L²(ν)` with
`∫ f dν = 0`. Then (`inner_centeredGreenOperator_self`)
`⟪G f, f⟫ = ∫_0^∞ ∫_{K₀} (∫ k_{s/2}(x, z) f(x) ν(dx))² dz ds ≥ 0`:
writing `g(x, y) = ∫_0^∞ (k_s(x, y) - 1) ds`, Fubini's theorem (with the integrable majorant
`a(s) |x - y|^{-2θ} + b(s)`) exchanges the time integral and the integral against `f ⊗ f ν ⊗ ν`
(`integral_greenOperator_eq_setIntegral`), the constant drops out since `∫ f = 0`, and the
Chapman–Kolmogorov identity `k_s(x, y) = ∫ k_{s/2}(x, z) k_{s/2}(z, y) dz` writes the remaining
integral as an integral of squares (`integral_prod_neumannKernel_mul_eq`).

If `⟪G f, f⟫ = 0`, the squares vanish for almost every `s > 0`; along such `s → 0`,
`∫ f(x) E_x ψ(b_{s/2}) ν(dx) = 0` for every bounded continuous `ψ`, and `E_x ψ(b_t) → ψ(x)` as
`t → 0` by continuity of the paths, so `∫ f ψ dν = 0` for all bounded continuous `ψ`; these are
dense in `L²(ν)`, so `f = 0` (`eq_zero_of_inner_centeredGreenOperator_self_eq_zero`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction

namespace HarmonicBalls

variable {ν : Measure ℂ}

/-! ### Products of square-integrable rows -/

theorem abs_mul_le_add_sq_div_two (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

variable [IsProbabilityMeasure ν]

/-- **Integrability on `ν ⊗ ν`** of `k(x, y) u(x) v(y)` for a kernel whose rows are uniformly
bounded in `L²(ν)` and `u, v ∈ L²(ν)`. -/
theorem integrable_prod_kernel_mul {k : ℂ → ℂ → ℝ} (hk : Measurable fun p : ℂ × ℂ => k p.1 p.2)
    {R : ℝ} (hkR : ∀ᵐ x ∂ν, MemLp (k x) 2 ν ∧ ∫ y, k x y ^ 2 ∂ν ≤ R)
    {u v : ℂ → ℝ} (hu : MemLp u 2 ν) (hv : MemLp v 2 ν) :
    Integrable (fun p : ℂ × ℂ => k p.1 p.2 * (u p.1 * v p.2)) (ν.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : ℂ × ℂ => k p.1 p.2 * (u p.1 * v p.2)) (ν.prod ν) :=
    hk.aestronglyMeasurable.mul (hu.aestronglyMeasurable.comp_fst.mul hv.aestronglyMeasurable.comp_snd)
  have hrow : ∀ x, MemLp (k x) 2 ν → Integrable (fun y => k x y * v y) ν := by
    intro x hx
    have hkx : Measurable (k x) := hk.comp (measurable_const.prodMk measurable_id)
    refine ((hx.integrable_sq.add hv.integrable_sq).div_const 2).mono'
      (hkx.aestronglyMeasurable.mul hv.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, Pi.add_apply]
    exact abs_mul_le_add_sq_div_two _ _
  refine (integrable_prod_iff hm).2 ⟨?_, ?_⟩
  · filter_upwards [hkR] with x hx
    exact ((hrow x hx.1).const_mul (u x)).congr (Eventually.of_forall fun y => by
      simp only; ring)
  · have hb : Integrable (fun x => |u x| * ((R + ∫ y, v y ^ 2 ∂ν) / 2)) ν :=
      (hu.integrable one_le_two).abs.mul_const _
    refine hb.mono' hm.norm.integral_prod_right' ?_
    filter_upwards [hkR] with x hx
    have hi := hrow x hx.1
    have e : (fun y => ‖k x y * (u x * v y)‖) = fun y => |u x| * |k x y * v y| := by
      funext y
      simp only [Real.norm_eq_abs, abs_mul]
      ring
    rw [e, integral_const_mul, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc ∫ y, |k x y * v y| ∂ν ≤ ∫ y, (k x y ^ 2 + v y ^ 2) / 2 ∂ν :=
          integral_mono_ae hi.abs ((hx.1.integrable_sq.add hv.integrable_sq).div_const 2)
            (Eventually.of_forall fun y => abs_mul_le_add_sq_div_two _ _)
      _ = ((∫ y, k x y ^ 2 ∂ν) + ∫ y, v y ^ 2 ∂ν) / 2 := by
          rw [integral_div, integral_add hx.1.integrable_sq hv.integrable_sq]
      _ ≤ (R + ∫ y, v y ^ 2 ∂ν) / 2 := by linarith [hx.2]

/-- Almost every pair is off the diagonal of `K₀`. -/
theorem IsUpperRegularSpeed.ae_prod_offDiag (hν : IsUpperRegularSpeed ν) :
    ∀ᵐ p ∂(ν.prod ν), p.1 ∈ closedSquare (0 : ℂ) 1 ∧ p.2 ∈ closedSquare (0 : ℂ) 1 ∧
      p.1 ≠ p.2 := by
  have hS : MeasurableSet {p : ℂ × ℂ | p.1 ∈ closedSquare (0 : ℂ) 1 ∧
      p.2 ∈ closedSquare (0 : ℂ) 1 ∧ p.1 ≠ p.2} :=
    (measurableSet_closedSquare_zero_one.preimage measurable_fst).inter
      ((measurableSet_closedSquare_zero_one.preimage measurable_snd).inter
        measurableSet_diagonal.compl)
  refine (Measure.ae_prod_mem_iff_ae_ae_mem hS).2 ?_
  filter_upwards [hν.ae_mem] with x hx
  filter_upwards [hν.ae_mem, hν.ae_ne hx] with y hy hyx
  exact ⟨hx, hy, Ne.symm hyx⟩

/-- Rows of a kernel bounded on `K₀ × K₀`. -/
theorem IsUpperRegularSpeed.ae_memLp_of_bounded (hν : IsUpperRegularSpeed ν) {k : ℂ → ℂ → ℝ}
    (hk : Measurable fun p : ℂ × ℂ => k p.1 p.2) {C : ℝ}
    (hC : ∀ x ∈ closedSquare (0 : ℂ) 1, ∀ y ∈ closedSquare (0 : ℂ) 1, |k x y| ≤ C) :
    ∀ᵐ x ∂ν, MemLp (k x) 2 ν ∧ ∫ y, k x y ^ 2 ∂ν ≤ C ^ 2 := by
  filter_upwards [hν.ae_mem] with x hx
  have hkx : Measurable (k x) := hk.comp (measurable_const.prodMk measurable_id)
  have hb : ∀ᵐ y ∂ν, k x y ∈ Icc (-C) C := by
    filter_upwards [hν.ae_mem] with y hy
    exact abs_le.1 (hC x hx y hy)
  have hm : MemLp (k x) 2 ν := memLp_of_bounded hb hkx.aestronglyMeasurable 2
  refine ⟨hm, ?_⟩
  calc ∫ y, k x y ^ 2 ∂ν ≤ ∫ _, C ^ 2 ∂ν := integral_mono_ae hm.integrable_sq (integrable_const _)
        (hb.mono fun y h => sq_le_sq' h.1 h.2)
    _ = C ^ 2 := by simp

/-! ### The time integral -/

/-- **Exchanging the time integral**: for `f ∈ L²(ν)`,
`∫∫ g(x, y) f(x) f(y) = ∫_0^∞ ∫∫ (k_s(x, y) - 1) f(x) f(y) ds`, and the time integrand is
integrable. -/
theorem IsUpperRegularSpeed.integral_greenOperator_eq_setIntegral (hν : IsUpperRegularSpeed ν)
    (f : Lp ℝ 2 ν) :
    IntegrableOn (fun s => ∫ p, (neumannKernel s p.1 p.2 - 1) *
        ((f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2) ∂(ν.prod ν)) (Ioi 0) ∧
      ∫ x, (∫ y, centeredGreenKernel x y * (f : ℂ → ℝ) y ∂ν) * (f : ℂ → ℝ) x ∂ν =
        ∫ s in Ioi (0 : ℝ), ∫ p, (neumannKernel s p.1 p.2 - 1) *
          ((f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2) ∂(ν.prod ν) := by
  obtain ⟨β, hβ, hR⟩ := hν.exists_riesz_le
  obtain ⟨θ, hθ0, hθ1, hθβ⟩ := exists_theta hβ
  obtain ⟨R, hR0, hRx⟩ := hR (4 * θ) (by positivity) hθβ
  obtain ⟨a, b, ham, hbm, hai, hbi, ha0, hb0, hab⟩ := exists_neumannKernel_majorant hθ0 hθ1
  obtain ⟨B₀, -, hB⟩ := hν.exists_memLp_centeredGreenKernel
  have hf2 : MemLp (f : ℂ → ℝ) 2 ν := Lp.memLp f
  -- the weight `w(x, y) = |x - y|^{-2θ}`
  set w : ℂ → ℂ → ℝ := fun x y => ‖x - y‖ ^ (-(2 * θ)) with hw
  have hwm : Measurable fun p : ℂ × ℂ => w p.1 p.2 := by
    simp only [hw]
    fun_prop
  have hwR : ∀ᵐ x ∂ν, MemLp (w x) 2 ν ∧ ∫ y, w x y ^ 2 ∂ν ≤ R := by
    filter_upwards [hν.ae_mem] with x hx
    have hi := integrable_rpow_neg_of_lintegral (hRx x hx)
    have hsq : (fun y => w x y ^ 2) = fun y => ‖x - y‖ ^ (-(4 * θ)) := by
      funext y; simp only [hw]; exact rpow_neg_two_mul_sq _ _
    have hwxm : Measurable (w x) := hwm.comp (measurable_const.prodMk measurable_id)
    refine ⟨(memLp_two_iff_integrable_sq hwxm.aestronglyMeasurable).2 (by rw [hsq]; exact hi), ?_⟩
    rw [hsq]
    exact integral_rpow_neg_le_of_lintegral hR0 (hRx x hx)
  have hW := integrable_prod_kernel_mul hwm hwR hf2.abs hf2.abs
  have hU : Integrable (fun p : ℂ × ℂ => |(f : ℂ → ℝ) p.1| * |(f : ℂ → ℝ) p.2|) (ν.prod ν) :=
    ((hf2.integrable one_le_two).abs).mul_prod ((hf2.integrable one_le_two).abs)
  have hgR : ∀ᵐ x ∂ν, MemLp (centeredGreenKernel x) 2 ν ∧
      ∫ y, centeredGreenKernel x y ^ 2 ∂ν ≤ B₀ := by
    filter_upwards [hν.ae_mem] with x hx
    exact hB x hx
  have hG := integrable_prod_kernel_mul measurable_centeredGreenKernel_uncurry hgR hf2 hf2
  -- the function on the triple product
  set F : (ℂ × ℂ) × ℝ → ℝ := fun q => (neumannKernel q.2 q.1.1 q.1.2 - 1) *
    ((f : ℂ → ℝ) q.1.1 * (f : ℂ → ℝ) q.1.2) with hF
  have hFm : AEStronglyMeasurable F ((ν.prod ν).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    ((measurable_neumannKernel_uncurry.comp (measurable_snd.prodMk
      (measurable_fst.fst.prodMk measurable_fst.snd))).sub measurable_const).aestronglyMeasurable.mul
      ((hf2.aestronglyMeasurable.comp_fst.comp_fst).mul (hf2.aestronglyMeasurable.comp_snd.comp_fst))
  have hmaj : Integrable (fun q : (ℂ × ℂ) × ℝ =>
      w q.1.1 q.1.2 * (|(f : ℂ → ℝ) q.1.1| * |(f : ℂ → ℝ) q.1.2|) * a q.2 +
        |(f : ℂ → ℝ) q.1.1| * |(f : ℂ → ℝ) q.1.2| * b q.2)
      ((ν.prod ν).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (hW.mul_prod hai).add (hU.mul_prod hbi)
  have hoff : ∀ᵐ q ∂((ν.prod ν).prod (volume.restrict (Ioi (0 : ℝ)))),
      (q.1.1 ∈ closedSquare (0 : ℂ) 1 ∧ q.1.2 ∈ closedSquare (0 : ℂ) 1 ∧ q.1.1 ≠ q.1.2) ∧
        0 < q.2 := by
    have h1 : ∀ᵐ q ∂((ν.prod ν).prod (volume.restrict (Ioi (0 : ℝ)))),
        q.1.1 ∈ closedSquare (0 : ℂ) 1 ∧ q.1.2 ∈ closedSquare (0 : ℂ) 1 ∧ q.1.1 ≠ q.1.2 :=
      Measure.quasiMeasurePreserving_fst.ae hν.ae_prod_offDiag
    have h2 : ∀ᵐ q ∂((ν.prod ν).prod (volume.restrict (Ioi (0 : ℝ)))), q.2 ∈ Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [h1, h2] with q hq1 hq2
    exact ⟨hq1, hq2⟩
  have hint : Integrable F ((ν.prod ν).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine hmaj.mono' hFm ?_
    filter_upwards [hoff] with q hq
    obtain ⟨⟨hx, hy, hxy⟩, hs⟩ := hq
    simp only [hF, Real.norm_eq_abs, abs_mul]
    have h := hab q.1.1 hx q.1.2 hy hxy q.2 hs
    have hff : 0 ≤ |(f : ℂ → ℝ) q.1.1| * |(f : ℂ → ℝ) q.1.2| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc |neumannKernel q.2 q.1.1 q.1.2 - 1| * (|(f : ℂ → ℝ) q.1.1| * |(f : ℂ → ℝ) q.1.2|)
        ≤ (a q.2 * w q.1.1 q.1.2 + b q.2) * (|(f : ℂ → ℝ) q.1.1| * |(f : ℂ → ℝ) q.1.2|) :=
          mul_le_mul_of_nonneg_right h hff
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · have h := hint.integral_prod_right
    exact h
  -- the two iterated integrals
  have hswap := integral_integral_swap (μ := ν.prod ν) (ν := volume.restrict (Ioi (0 : ℝ)))
    (f := fun p s => F (p, s)) hint
  calc ∫ x, (∫ y, centeredGreenKernel x y * (f : ℂ → ℝ) y ∂ν) * (f : ℂ → ℝ) x ∂ν
      = ∫ p, centeredGreenKernel p.1 p.2 * ((f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2) ∂(ν.prod ν) := by
        rw [integral_prod _ hG]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show (∫ y, centeredGreenKernel x y * (f : ℂ → ℝ) y ∂ν) * (f : ℂ → ℝ) x =
          ∫ y, centeredGreenKernel x y * ((f : ℂ → ℝ) x * (f : ℂ → ℝ) y) ∂ν
        rw [← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        ring
    _ = ∫ p, (∫ s in Ioi (0 : ℝ), F (p, s)) ∂(ν.prod ν) := by
        refine integral_congr_ae ?_
        filter_upwards [hν.ae_prod_offDiag] with p hp
        simp only [hF]
        rw [integral_mul_const]
        rfl
    _ = ∫ s in Ioi (0 : ℝ), ∫ p, F (p, s) ∂(ν.prod ν) := hswap
    _ = _ := rfl

/-! ### The Chapman–Kolmogorov square -/

/-- **The square form**: for `s > 0`,
`∫∫ k_s(x, y) f(x) f(y) = ∫_{K₀} (∫ k_{s/2}(x, z) f(x) ν(dx))² dz`. -/
theorem IsUpperRegularSpeed.integral_prod_neumannKernel_mul_eq (hν : IsUpperRegularSpeed ν)
    (f : Lp ℝ 2 ν) {s : ℝ} (hs : 0 < s) :
    ∫ p, neumannKernel s p.1 p.2 * ((f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2) ∂(ν.prod ν) =
      ∫ z in closedSquare 0 1, (∫ x, neumannKernel (s / 2) x z * (f : ℂ → ℝ) x ∂ν) ^ 2 := by
  have hs2 : 0 < s / 2 := by positivity
  obtain ⟨C, hC0, hC⟩ := exists_neumannKernel_le hs2 le_rfl
  have hf2 : MemLp (f : ℂ → ℝ) 2 ν := Lp.memLp f
  have hf1 : Integrable (f : ℂ → ℝ) ν := hf2.integrable one_le_two
  have hk : Measurable fun p : ℂ × ℂ => neumannKernel (s / 2) p.1 p.2 :=
    measurable_neumannKernel_uncurry.comp (measurable_const.prodMk measurable_id)
  have hU : Integrable (fun p : ℂ × ℂ => |(f : ℂ → ℝ) p.1| * |(f : ℂ → ℝ) p.2|) (ν.prod ν) :=
    hf1.abs.mul_prod hf1.abs
  set T : (ℂ × ℂ) × ℂ → ℝ := fun q => neumannKernel (s / 2) q.1.1 q.2 *
    neumannKernel (s / 2) q.2 q.1.2 * ((f : ℂ → ℝ) q.1.1 * (f : ℂ → ℝ) q.1.2) with hT
  have hTm : AEStronglyMeasurable T ((ν.prod ν).prod (volume.restrict (closedSquare 0 1))) :=
    (((hk.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hk.comp (measurable_snd.prodMk measurable_fst.snd))).aestronglyMeasurable).mul
      ((hf2.aestronglyMeasurable.comp_fst.comp_fst).mul (hf2.aestronglyMeasurable.comp_snd.comp_fst))
  have hKz : ∀ᵐ q ∂((ν.prod ν).prod (volume.restrict (closedSquare (0 : ℂ) 1))),
      q.1.1 ∈ closedSquare (0 : ℂ) 1 ∧ q.1.2 ∈ closedSquare (0 : ℂ) 1 ∧
        q.2 ∈ closedSquare (0 : ℂ) 1 := by
    have h1 : ∀ᵐ q ∂((ν.prod ν).prod (volume.restrict (closedSquare (0 : ℂ) 1))),
        q.1.1 ∈ closedSquare (0 : ℂ) 1 ∧ q.1.2 ∈ closedSquare (0 : ℂ) 1 ∧ q.1.1 ≠ q.1.2 :=
      Measure.quasiMeasurePreserving_fst.ae hν.ae_prod_offDiag
    have h2 : ∀ᵐ q ∂((ν.prod ν).prod (volume.restrict (closedSquare (0 : ℂ) 1))),
        q.2 ∈ closedSquare (0 : ℂ) 1 :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_closedSquare_zero_one)
    filter_upwards [h1, h2] with q hq1 hq2
    exact ⟨hq1.1, hq1.2.1, hq2⟩
  have hTi : Integrable T ((ν.prod ν).prod (volume.restrict (closedSquare 0 1))) := by
    refine ((hU.mul_prod (integrable_const (C * C)))).mono' hTm ?_
    filter_upwards [hKz] with q hq
    obtain ⟨hx, hy, hz⟩ := hq
    simp only [hT, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (neumannKernel_nonneg _ _ _), abs_of_nonneg (neumannKernel_nonneg _ _ _)]
    have h1 := hC _ ⟨le_rfl, le_rfl⟩ _ hx _ hz
    have h2 := hC _ ⟨le_rfl, le_rfl⟩ _ hz _ hy
    have hff : 0 ≤ |(f : ℂ → ℝ) q.1.1| * |(f : ℂ → ℝ) q.1.2| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc neumannKernel (s / 2) q.1.1 q.2 * neumannKernel (s / 2) q.2 q.1.2 *
          (|(f : ℂ → ℝ) q.1.1| * |(f : ℂ → ℝ) q.1.2|)
        ≤ C * C * (|(f : ℂ → ℝ) q.1.1| * |(f : ℂ → ℝ) q.1.2|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (neumannKernel_nonneg _ _ _) hC0) hff
      _ = _ := by ring
  have hswap := integral_integral_swap (μ := ν.prod ν)
    (ν := volume.restrict (closedSquare (0 : ℂ) 1)) (f := fun p z => T (p, z)) hTi
  calc ∫ p, neumannKernel s p.1 p.2 * ((f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2) ∂(ν.prod ν)
      = ∫ p, (∫ z in closedSquare 0 1, T (p, z)) ∂(ν.prod ν) := by
        refine integral_congr_ae ?_
        filter_upwards [hν.ae_prod_offDiag] with p hp
        obtain ⟨hx, hy, -⟩ := hp
        have hck := neumannKernel_add hs2 hs2 hx hy
        rw [add_halves] at hck
        rw [hck, ← integral_mul_const]
    _ = ∫ z in closedSquare 0 1, ∫ p, T (p, z) ∂(ν.prod ν) := hswap
    _ = ∫ z in closedSquare 0 1, (∫ x, neumannKernel (s / 2) x z * (f : ℂ → ℝ) x ∂ν) ^ 2 := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        have e : (fun p : ℂ × ℂ => T (p, z)) = fun p => (neumannKernel (s / 2) p.1 z *
            (f : ℂ → ℝ) p.1) * (neumannKernel (s / 2) p.2 z * (f : ℂ → ℝ) p.2) := by
          funext p
          simp only [hT]
          rw [neumannKernel_comm (s / 2) z p.2]
          ring
        simp only
        rw [e, integral_prod_mul (fun x => neumannKernel (s / 2) x z * (f : ℂ → ℝ) x)
          (fun x => neumannKernel (s / 2) x z * (f : ℂ → ℝ) x), sq]

/-! ### The law of the reflected motion against bounded functions -/

/-- `E_x ψ(b_t) = ∫_{K₀} k_t(x, z) ψ(z) dz` for bounded measurable `ψ`, `x ∈ K₀`, `t > 0`. -/
theorem integral_reflected_eval_eq {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) {t : ℝ}
    (ht : 0 < t) {ψ : ℂ → ℝ} (hψ : Measurable ψ) :
    ∫ b, ψ (b t.toNNReal) ∂reflectedPlanarBrownianMotion 0 1 x =
      ∫ z in closedSquare 0 1, neumannKernel t x z * ψ z := by
  have ht' : t.toNNReal ≠ 0 := (Real.toNNReal_pos.2 ht).ne'
  have hkm : Measurable fun z => ENNReal.ofReal (neumannKernel t x z) :=
    ENNReal.measurable_ofReal.comp (measurable_neumannKernel t x)
  have hmap : (reflectedPlanarBrownianMotion 0 1 x).map (fun b => b t.toNNReal) =
      (volume.restrict (closedSquare (0 : ℂ) 1)).withDensity
        fun z => ENNReal.ofReal (neumannKernel t x z) := by
    ext S hS
    rw [Measure.map_apply (continuous_eval_const _).measurable hS, withDensity_apply _ hS]
    have h := lintegral_reflected_eval_eq_neumannKernel (Φ := S.indicator 1)
      (measurable_one.indicator hS) x ht'
    rw [← lintegral_indicator_one ((continuous_eval_const _).measurable hS)]
    calc ∫⁻ b, ((fun b : ContinuousPath ℂ => b t.toNNReal) ⁻¹' S).indicator 1 b
          ∂reflectedPlanarBrownianMotion 0 1 x
        = ∫⁻ b, S.indicator 1 (b t.toNNReal) ∂reflectedPlanarBrownianMotion 0 1 x := by
          refine lintegral_congr fun b => ?_
          by_cases hb : b t.toNNReal ∈ S <;> simp [indicator, hb]
      _ = ∫⁻ z in closedSquare 0 1, S.indicator 1 z * squareNeumannKernel t.toNNReal x z := h
      _ = ∫⁻ z in S, ENNReal.ofReal (neumannKernel t x z) ∂volume.restrict (closedSquare 0 1) := by
          rw [← lintegral_indicator hS]
          refine setLIntegral_congr_fun measurableSet_closedSquare_zero_one fun z hz => ?_
          by_cases hzS : z ∈ S <;> simp [indicator, hzS, ofReal_neumannKernel ht hx hz]
  have hfin : ∀ᵐ z ∂volume.restrict (closedSquare (0 : ℂ) 1),
      ENNReal.ofReal (neumannKernel t x z) < ∞ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [← integral_map (continuous_eval_const _).measurable.aemeasurable hψ.aestronglyMeasurable,
    hmap, integral_withDensity_eq_integral_toReal_smul hkm hfin]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show (ENNReal.ofReal (neumannKernel t x z)).toReal • ψ z = neumannKernel t x z * ψ z
  rw [ENNReal.toReal_ofReal (neumannKernel_nonneg _ _ _), smul_eq_mul]

/-- **The reflected motion starts at its start**: `E_x ψ(b_{t_n}) → ψ(x)` for continuous bounded
`ψ` and times `t_n → 0`. -/
theorem tendsto_integral_reflected_eval {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) (ψ : ℂ →ᵇ ℝ)
    {t : ℕ → ℝ≥0} (htl : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ∫ b, ψ (b (t n)) ∂reflectedPlanarBrownianMotion 0 1 x) atTop (𝓝 (ψ x)) := by
  have h := tendsto_integral_of_dominated_convergence (μ := reflectedPlanarBrownianMotion 0 1 x)
    (F := fun n b => ψ (b (t n))) (f := fun b => ψ (b 0)) (fun _ => ‖ψ‖)
    (fun n => (ψ.continuous.measurable.comp (continuous_eval_const _).measurable).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall fun b => ψ.norm_coe_le_norm _)
    (Eventually.of_forall fun b => (ψ.continuous.tendsto _).comp ((b.continuous.tendsto 0).comp htl))
  have h0 : ∫ b, ψ (b 0) ∂reflectedPlanarBrownianMotion 0 1 x = ψ x := by
    rw [integral_congr_ae ((ae_reflected_eval_zero hx).mono fun b hb => by rw [hb])]
    simp
  rwa [h0] at h

/-! ### Positivity and injectivity -/

/-- **`⟪G f, f⟫ ≥ 0`**, and the time integrand is a nonnegative integrable function, for
`f` of mean zero. -/
theorem IsUpperRegularSpeed.inner_centeredGreenOperator_self (hν : IsUpperRegularSpeed ν)
    {f : Lp ℝ 2 ν} (hf : ⟪oneLp ν, f⟫_ℝ = 0) :
    IntegrableOn (fun s => ∫ p, (neumannKernel s p.1 p.2 - 1) *
        ((f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2) ∂(ν.prod ν)) (Ioi 0) ∧
      (∀ s, 0 < s → ∫ p, (neumannKernel s p.1 p.2 - 1) * ((f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2)
          ∂(ν.prod ν) =
        ∫ z in closedSquare 0 1, (∫ x, neumannKernel (s / 2) x z * (f : ℂ → ℝ) x ∂ν) ^ 2) ∧
      ⟪centeredGreenOperator hν f, f⟫_ℝ = ∫ s in Ioi (0 : ℝ), ∫ p, (neumannKernel s p.1 p.2 - 1) *
        ((f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2) ∂(ν.prod ν) := by
  obtain ⟨hint, hEq⟩ := hν.integral_greenOperator_eq_setIntegral f
  have hf2 : MemLp (f : ℂ → ℝ) 2 ν := Lp.memLp f
  have hf1 : Integrable (f : ℂ → ℝ) ν := hf2.integrable one_le_two
  have hmean : ∫ x, (f : ℂ → ℝ) x ∂ν = 0 := by rw [← inner_oneLp_left]; exact hf
  refine ⟨hint, fun s hs => ?_, ?_⟩
  · have hs2 : 0 < s / 2 := by positivity
    obtain ⟨C, hC0, hC⟩ := exists_neumannKernel_le hs le_rfl
    have hk : Measurable fun p : ℂ × ℂ => neumannKernel s p.1 p.2 :=
      measurable_neumannKernel_uncurry.comp (measurable_const.prodMk measurable_id)
    have hkR := hν.ae_memLp_of_bounded hk (C := C) fun x hx y hy => by
      rw [abs_of_nonneg (neumannKernel_nonneg _ _ _)]; exact hC s ⟨le_rfl, le_rfl⟩ x hx y hy
    have h1 := integrable_prod_kernel_mul hk hkR hf2 hf2
    have h2 : Integrable (fun p : ℂ × ℂ => (f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2) (ν.prod ν) :=
      hf1.mul_prod hf1
    have e : (fun p : ℂ × ℂ => (neumannKernel s p.1 p.2 - 1) *
        ((f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2)) = fun p => neumannKernel s p.1 p.2 *
          ((f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2) - (f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2 := by
      funext p; ring
    rw [e, integral_sub h1 h2, integral_prod_mul, hmean, mul_zero, sub_zero,
      hν.integral_prod_neumannKernel_mul_eq f hs]
  · have hQ : meanZeroProj ν f = f := meanZeroProj_of_inner_eq_zero hf
    have h1 : ⟪centeredGreenOperator hν f, f⟫_ℝ = ⟪greenOperator hν f, f⟫_ℝ := by
      simp only [centeredGreenOperator, ContinuousLinearMap.comp_apply]
      rw [inner_meanZeroProj_comm, hQ]
    rw [h1, greenOperator, inner_rowOperator_left, ← hEq]
    refine integral_congr_ae ?_
    filter_upwards [hν.ae_mem] with x hx
    rw [hν.inner_greenRow hx]

/-- **Injectivity of `G` on the functions of mean zero**: if `⟪G f, f⟫ = 0` then `f = 0`. -/
theorem IsUpperRegularSpeed.eq_zero_of_inner_centeredGreenOperator_self_eq_zero
    (hν : IsUpperRegularSpeed ν) {f : Lp ℝ 2 ν} (hf : ⟪oneLp ν, f⟫_ℝ = 0)
    (h0 : ⟪centeredGreenOperator hν f, f⟫_ℝ = 0) : f = 0 := by
  obtain ⟨hint, hsq, hEq⟩ := hν.inner_centeredGreenOperator_self hf
  have hf2 : MemLp (f : ℂ → ℝ) 2 ν := Lp.memLp f
  have hf1 : Integrable (f : ℂ → ℝ) ν := hf2.integrable one_le_two
  set H : ℝ → ℝ := fun s => ∫ p, (neumannKernel s p.1 p.2 - 1) *
    ((f : ℂ → ℝ) p.1 * (f : ℂ → ℝ) p.2) ∂(ν.prod ν) with hH
  -- the time integrand vanishes almost everywhere
  have hHnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] H :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => by
      simp only [hH, Pi.zero_apply]
      rw [hsq s hs]; exact setIntegral_nonneg measurableSet_closedSquare_zero_one
        fun _ _ => sq_nonneg _)
  have hH0 : H =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hHnn hint).1 (by rw [← hEq]; exact h0)
  -- along a sequence `s_n → 0` with `H(s_n) = 0`
  have hseq : ∀ n : ℕ, ∃ s ∈ Ioo (0 : ℝ) (1 / (n + 1)), H s = 0 := by
    intro n
    by_contra hcon
    push Not at hcon
    have hpos : 0 < volume (Ioo (0 : ℝ) (1 / (n + 1))) := by
      rw [Real.volume_Ioo]; simp only [sub_zero, ENNReal.ofReal_pos]; positivity
    have hnull : volume (Ioo (0 : ℝ) (1 / (n + 1))) = 0 := by
      have h := (ae_restrict_iff' measurableSet_Ioi).1 hH0
      rw [ae_iff] at h
      refine measure_mono_null (fun s hs => ?_) h
      exact fun h' => hcon s hs (by simpa using h' hs.1)
    exact hpos.ne' hnull
  choose s hs hHs using hseq
  -- the squares vanish, so `∫ f(x) E_x ψ(b_{s_n/2}) ν(dx) = 0`
  have hfm : Measurable (f : ℂ → ℝ) := (Lp.stronglyMeasurable f).measurable
  have hkey : ∀ (ψ : ℂ →ᵇ ℝ) (n : ℕ), ∫ x, (f : ℂ → ℝ) x *
      ∫ b, ψ (b (s n / 2).toNNReal) ∂reflectedPlanarBrownianMotion 0 1 x ∂ν = 0 := by
    intro ψ n
    have hsn : 0 < s n := (hs n).1
    have hs2 : 0 < s n / 2 := by positivity
    obtain ⟨C, hC0, hC⟩ := exists_neumannKernel_le hs2 le_rfl
    have hk2 : Measurable fun q : ℂ × ℂ => neumannKernel (s n / 2) q.1 q.2 :=
      measurable_neumannKernel_uncurry.comp (measurable_const.prodMk measurable_id)
    set Ψ : ℂ → ℝ := fun z => ∫ x, neumannKernel (s n / 2) x z * (f : ℂ → ℝ) x ∂ν with hΨ
    have hΨm : Measurable Ψ := by
      have hm : StronglyMeasurable fun q : ℂ × ℂ => neumannKernel (s n / 2) q.2 q.1 *
          (f : ℂ → ℝ) q.2 :=
        ((hk2.comp (measurable_snd.prodMk measurable_fst)).mul
          (hfm.comp measurable_snd)).stronglyMeasurable
      exact (hm.integral_prod_right' (ν := ν)).measurable
    have hΨb : ∀ z ∈ closedSquare (0 : ℂ) 1, |Ψ z| ≤ C * ∫ x, |(f : ℂ → ℝ) x| ∂ν := by
      intro z hz
      calc |Ψ z| ≤ ∫ x, |neumannKernel (s n / 2) x z * (f : ℂ → ℝ) x| ∂ν :=
            abs_integral_le_integral_abs
        _ ≤ ∫ x, C * |(f : ℂ → ℝ) x| ∂ν := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
              (hf1.abs.const_mul C) ?_
            filter_upwards [hν.ae_mem] with x hx
            rw [abs_mul, abs_of_nonneg (neumannKernel_nonneg _ _ _)]
            exact mul_le_mul_of_nonneg_right (hC _ ⟨le_rfl, le_rfl⟩ x hx z hz) (abs_nonneg _)
        _ = C * ∫ x, |(f : ℂ → ℝ) x| ∂ν := integral_const_mul _ _
    have hΨ2i : IntegrableOn (fun z => Ψ z ^ 2) (closedSquare 0 1) := by
      refine integrableOn_closedSquare_of_abs_le (hΨm.pow_const 2).aestronglyMeasurable
        (C := (C * ∫ x, |(f : ℂ → ℝ) x| ∂ν) ^ 2) fun z hz => ?_
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hΨb z hz) 2
    have hΨ0 : Ψ =ᵐ[volume.restrict (closedSquare (0 : ℂ) 1)] 0 := by
      have h := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun z => sq_nonneg (Ψ z))
        hΨ2i).1 (by rw [← hsq (s n) hsn]; exact hHs n)
      filter_upwards [h] with z hz
      exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hz
    -- Fubini against `ψ`
    set D : ℂ → ℂ → ℝ := fun x z => (f : ℂ → ℝ) x * neumannKernel (s n / 2) x z * ψ z with hD
    have hDm : AEStronglyMeasurable (Function.uncurry D) (ν.prod (volume.restrict
        (closedSquare (0 : ℂ) 1))) :=
      (((hfm.comp measurable_fst).mul hk2).mul (ψ.continuous.measurable.comp
        measurable_snd)).aestronglyMeasurable
    have hDi : Integrable (Function.uncurry D) (ν.prod (volume.restrict
        (closedSquare (0 : ℂ) 1))) := by
      refine (hf1.abs.mul_prod (integrable_const (C * ‖ψ‖))).mono' hDm ?_
      have h1 : ∀ᵐ q ∂(ν.prod (volume.restrict (closedSquare (0 : ℂ) 1))),
          q.1 ∈ closedSquare (0 : ℂ) 1 := Measure.quasiMeasurePreserving_fst.ae hν.ae_mem
      have h2 : ∀ᵐ q ∂(ν.prod (volume.restrict (closedSquare (0 : ℂ) 1))),
          q.2 ∈ closedSquare (0 : ℂ) 1 :=
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_closedSquare_zero_one)
      filter_upwards [h1, h2] with q hq1 hq2
      simp only [Function.uncurry, hD, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg (neumannKernel_nonneg _ _ _)]
      have hk := hC _ ⟨le_rfl, le_rfl⟩ _ hq1 _ hq2
      have hψ : |ψ q.2| ≤ ‖ψ‖ := by rw [← Real.norm_eq_abs]; exact ψ.norm_coe_le_norm _
      calc |(f : ℂ → ℝ) q.1| * neumannKernel (s n / 2) q.1 q.2 * |ψ q.2|
          ≤ |(f : ℂ → ℝ) q.1| * C * ‖ψ‖ := by
            gcongr
        _ = |(f : ℂ → ℝ) q.1| * (C * ‖ψ‖) := by ring
    have hswap := integral_integral_swap hDi
    calc ∫ x, (f : ℂ → ℝ) x * ∫ b, ψ (b (s n / 2).toNNReal) ∂reflectedPlanarBrownianMotion 0 1 x ∂ν
        = ∫ x, (∫ z in closedSquare 0 1, D x z) ∂ν := by
          refine integral_congr_ae ?_
          filter_upwards [hν.ae_mem] with x hx
          rw [integral_reflected_eval_eq hx hs2 ψ.continuous.measurable, ← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          simp only [hD]
          ring
      _ = ∫ z in closedSquare 0 1, ∫ x, D x z ∂ν := hswap
      _ = ∫ z in closedSquare 0 1, Ψ z * ψ z := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          simp only [hD, hΨ]
          rw [← integral_mul_const]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only
          ring
      _ = 0 := by
          rw [integral_congr_ae (hΨ0.mono fun z hz => by rw [hz, Pi.zero_apply, zero_mul])]
          simp
  -- the limit `s_n → 0`
  have htn : Tendsto (fun n => (s n / 2).toNNReal) atTop (𝓝 0) := by
    have h1 : Tendsto s atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hs n).1.le) (fun n => (hs n).2.le)
    have h3 := h1.div_const 2
    rw [zero_div] at h3
    have h2 := (continuous_real_toNNReal.tendsto 0).comp h3
    rw [Real.toNNReal_zero] at h2
    exact h2
  have hψ : ∀ ψ : ℂ →ᵇ ℝ, ∫ x, (f : ℂ → ℝ) x * ψ x ∂ν = 0 := by
    intro ψ
    have h := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun n x => (f : ℂ → ℝ) x * ∫ b, ψ (b (s n / 2).toNNReal)
        ∂reflectedPlanarBrownianMotion 0 1 x)
      (f := fun x => (f : ℂ → ℝ) x * ψ x) (fun x => |(f : ℂ → ℝ) x| * ‖ψ‖)
      (fun n => by
        have hm : StronglyMeasurable fun x => ∫ b, ψ (b (s n / 2).toNNReal)
            ∂reflectedPlanarBrownianMotion 0 1 x := by
          have hg : StronglyMeasurable fun q : ℂ × ContinuousPath ℂ => ψ (q.2 (s n / 2).toNNReal) :=
            (ψ.continuous.measurable.comp ((continuous_eval_const _).measurable.comp
              measurable_snd)).stronglyMeasurable
          exact hg.integral_kernel_prod_right'
        exact (hfm.aestronglyMeasurable.mul hm.aestronglyMeasurable))
      (hf1.abs.mul_const _)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc |∫ b, ψ (b (s n / 2).toNNReal) ∂reflectedPlanarBrownianMotion 0 1 x|
            ≤ ∫ b, |ψ (b (s n / 2).toNNReal)| ∂reflectedPlanarBrownianMotion 0 1 x :=
              abs_integral_le_integral_abs
          _ ≤ ∫ _, ‖ψ‖ ∂reflectedPlanarBrownianMotion 0 1 x :=
              integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
                (integrable_const _) (Eventually.of_forall fun b => by
                  show |ψ (b (s n / 2).toNNReal)| ≤ ‖ψ‖
                  rw [← Real.norm_eq_abs]; exact ψ.norm_coe_le_norm _)
          _ = ‖ψ‖ := by simp)
      (by
        filter_upwards [hν.ae_mem] with x hx
        exact (tendsto_integral_reflected_eval hx ψ htn).const_mul _)
    have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (∫ x, (f : ℂ → ℝ) x * ψ x ∂ν)) :=
      h.congr fun n => hkey ψ n
    exact (tendsto_nhds_unique hconst tendsto_const_nhds)
  -- bounded continuous functions are dense in `L²(ν)`
  have hd := BoundedContinuousFunction.toLp_denseRange ℝ ν ℝ (p := 2) ENNReal.ofNat_ne_top
  have hzero : ∀ u : Lp ℝ 2 ν, ⟪f, u⟫_ℝ = 0 := by
    intro u
    refine hd.induction_on u (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
      fun ψ => ?_
    rw [l2_inner_eq_integral_mul]
    rw [← hψ ψ]
    refine integral_congr_ae ?_
    filter_upwards [BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℝ) ψ] with x hx
    rw [hx]
  exact inner_self_eq_zero.1 (hzero f)

end HarmonicBalls
