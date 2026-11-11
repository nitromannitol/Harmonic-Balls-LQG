import HarmonicBalls.FirstPass.Frozen.S11g
import HarmonicBalls.Steps.Sec11.WeylLocalEdges
import HarmonicBalls.Steps.Sec11.MetricArcLength
import HarmonicBalls.Steps.Sec11.WeylPathSegments
import HarmonicBalls.Steps.Sec11.WeylPathConcatenation
import HarmonicBalls.Steps.Sec11.WeylPathReverse

/-!
# The Weyl scaling of a Euclidean length metric is a Euclidean length metric

Derivation of `WeylScaledEuclideanFrozen` (`FirstPass/Frozen/S11g.lean:146`; row 57 of
`docs/campaign/PHASE2-INVENTORY.md`): if `D` is a Euclidean length metric on `ℂ` and `f` is continuous with compact
support, then for every real `ξ` the Weyl scaling `e^{ξ f} · D` (Gwynne-Miller, arXiv:1905.00383, (1.8), p. 6; paper
Fact 2.2 III, line 445) is again a Euclidean length metric (Fact 2.2 I, line 435). No hypothesis is added.

Route (`notes/fp-gaps/CHATGPT-hb-frozen-truth-0026.md`, section 5): the weight is bounded above and below by positive
constants `e^{∓K}`, so the weighted distance is bi-Lipschitz equivalent to `D` (`weylScaling` lies between `e^{-K} D`
and `e^{K} D`), which gives finiteness, separation and the topology. The metric axioms follow from reversal
(`weylScaling_symm`) and concatenation (`weylScaling_triangle`) of curves. The length property is
`IsEuclideanLengthMetric.weylScaling_internalMetric`.

The two comparison bounds are proved here from the arc-length reparametrization
(`exists_lengthParametrized_with_tracking`) and from the definition of `curveLength`.
-/

namespace HarmonicBalls

open Set MeasureTheory

/-- Upper comparison `weylScaling ≤ e^K · D` when `ξ f ≤ K` everywhere. Each path `P` from `x` to `y` is
reparametrized by its `D`-arclength; the reparametrized curve is a competitor in `weylScaling` of cost at most
`e^K` times its `D`-length. Taking the infimum over paths gives the bound with `D x y = internalMetric D univ x y`. -/
theorem IsEuclideanLengthMetric.weylScaling_le_exp_mul {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ K : ℝ} {f : ℂ → ℝ} (hw : ∀ z, ξ * f z ≤ K) (x y : ℂ) :
    weylScaling D ξ f x y ≤ ENNReal.ofReal (Real.exp K) * ENNReal.ofReal (D x y) := by
  have hc0 : ENNReal.ofReal (Real.exp K) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos K)).ne'
  have hP : ∀ P : Path x y, weylScaling D ξ f x y ≤ ENNReal.ofReal (Real.exp K) * pathLength D P := by
    intro P
    rcases eq_or_ne (curveLength D P.extend 0 1) ⊤ with htop | hfin
    · unfold pathLength
      rw [htop, ENNReal.mul_top hc0]
      exact le_top
    · have hlt : curveLength D P.extend 0 1 < ⊤ := lt_top_iff_ne_top.mpr hfin
      obtain ⟨q, hq, h0, hL, -⟩ :=
        hD.exists_lengthParametrized_with_tracking zero_le_one P.continuous_extend.continuousOn hlt
      have hle := weylScaling_le_of_lengthParametrized D ξ f hq (h0.trans P.extend_zero)
        (hL.trans P.extend_one) (fun t _ => hw (q t))
      rw [ENNReal.ofReal_toReal hfin] at hle
      exact hle
  have hinter : internalMetric D univ x y = ⨅ P : Path x y, pathLength D P := by
    unfold internalMetric
    simp only [mem_univ, forall_const, iInf_true]
  rw [hD.ofReal_eq_internalMetric x y, hinter, ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  exact le_iInf fun P => hP P

/-- Lower comparison `e^{-K} · D ≤ weylScaling` when `-K ≤ ξ f` everywhere. Each competitor `(T, p)` of `weylScaling`
has `T ≥ D x y` (the one-interval partition `{0, T}` in `curveLength D p 0 T = T`), and its weighted cost is at least
`e^{-K} T`. -/
theorem IsEuclideanLengthMetric.exp_mul_le_weylScaling {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ K : ℝ} {f : ℂ → ℝ} (hw : ∀ z, -K ≤ ξ * f z) (x y : ℂ) :
    ENNReal.ofReal (Real.exp (-K)) * ENNReal.ofReal (D x y) ≤ weylScaling D ξ f x y := by
  unfold weylScaling
  refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun hp0 => le_iInf fun hpT => ?_
  obtain ⟨hT0, -, hlen⟩ := hp
  have hcl : curveLength D p 0 T = ENNReal.ofReal T := by
    rw [hlen 0 T le_rfl hT0 le_rfl, sub_zero]
  let u : ℕ → ℝ := fun n => if n = 0 then 0 else T
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    rcases n with _ | n <;> simp [u, hT0]
  have humem : ∀ n, u n ∈ Icc (0 : ℝ) T := by
    intro n
    rcases n with _ | n <;> simp [u, hT0]
  have hle : ENNReal.ofReal (D (p T) (p 0)) ≤ curveLength D p 0 T := by
    unfold curveLength
    refine le_iSup_of_le (⟨1, ⟨u, hu, humem⟩⟩ : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0 : ℝ) T}) ?_
    simp [u]
  rw [hp0, hpT, hcl, hD.symm y x] at hle
  have hDT : D x y ≤ T := (ENNReal.ofReal_le_ofReal_iff hT0).mp hle
  calc ENNReal.ofReal (Real.exp (-K)) * ENNReal.ofReal (D x y)
      ≤ ENNReal.ofReal (Real.exp (-K)) * ENNReal.ofReal T := by
        gcongr
    _ = ∫⁻ _ in Icc 0 T, ENNReal.ofReal (Real.exp (-K)) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero]
    _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
        setLIntegral_mono' measurableSet_Icc fun t _ =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hw (p t)))

/-- **Derived** (task fp-phase2-weyl-scaled-euclidean-derive): the Weyl scaling `e^{ξ f} · D` of a Euclidean length
metric `D` by a continuous compactly supported `f` is a Euclidean length metric (`WeylScaledEuclideanFrozen`,
`FirstPass/Frozen/S11g.lean:146`). No hypothesis is added. -/
theorem weylScaledEuclidean_derived : WeylScaledEuclideanFrozen := by
  intro D ξ f hD hf hc
  -- `|f| ≤ B` by continuity and compact support (Mathlib's bound is on the norm)
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  obtain ⟨B, hfB⟩ : ∃ B : ℝ, ∀ z, |f z| ≤ B :=
    ⟨max C 0, fun z => (show |f z| ≤ C by simpa [Real.norm_eq_abs] using hC z).trans (le_max_left C 0)⟩
  -- `|ξ f| ≤ K := |ξ| B`
  set K : ℝ := |ξ| * B with hKdef
  have hξf : ∀ z, |ξ * f z| ≤ K := fun z => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hfB z) (abs_nonneg ξ)
  have hw1 : ∀ z, ξ * f z ≤ K := fun z => (abs_le.mp (hξf z)).2
  have hw2 : ∀ z, -K ≤ ξ * f z := fun z => (abs_le.mp (hξf z)).1
  have hup : ∀ x y, weylScaling D ξ f x y ≤ ENNReal.ofReal (Real.exp K) * ENNReal.ofReal (D x y) :=
    fun x y => hD.weylScaling_le_exp_mul hw1 x y
  have hlo : ∀ x y, ENNReal.ofReal (Real.exp (-K)) * ENNReal.ofReal (D x y) ≤ weylScaling D ξ f x y :=
    fun x y => hD.exp_mul_le_weylScaling hw2 x y
  have hfin : ∀ x y, weylScaling D ξ f x y ≠ ⊤ := fun x y =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hup x y)
  have hDnn : ∀ x y, 0 ≤ D x y := fun x y => by
    have h1 := hD.triangle x y x
    rw [hD.self_eq_zero x, hD.symm y x] at h1
    linarith
  -- the real Weyl scaling
  set E : ℂ → ℂ → ℝ := fun u v => (weylScaling D ξ f u v).toReal with hEdef
  have hE : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y :=
    fun x y => ENNReal.ofReal_toReal (hfin x y)
  have hEsymm : ∀ x y, E x y = E y x := fun x y => by
    show (weylScaling D ξ f x y).toReal = (weylScaling D ξ f y x).toReal
    rw [hD.weylScaling_symm ξ f x y]
  have hEge : ∀ x y, Real.exp (-K) * D x y ≤ E x y := fun x y => by
    have h := hlo x y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← hE x y] at h
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h
  have hEle : ∀ x y, E x y ≤ Real.exp K * D x y := fun x y => by
    have h := hup x y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← hE x y] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos K).le (hDnn x y))).mp h
  have hEmetric : IsEuclideanLengthMetric E := by
    refine ⟨?_, ?_, hEsymm, ?_, ?_, fun z w => hD.weylScaling_internalMetric ξ f hE hEsymm z w⟩
    · -- `D z z = 0` gives `weylScaling z z = 0`
      intro z
      have h := hup z z
      rw [hD.self_eq_zero z, ENNReal.ofReal_zero, mul_zero, nonpos_iff_eq_zero] at h
      show (weylScaling D ξ f z z).toReal = 0
      rw [h, ENNReal.toReal_zero]
    · -- separation: `E z w = 0` forces `weylScaling z w = 0`, hence `D z w = 0`
      intro z w hzw
      have hW : weylScaling D ξ f z w = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp hzw with h | h
        · exact h
        · exact absurd h (hfin z w)
      have h := hlo z w
      rw [hW, nonpos_iff_eq_zero] at h
      have hpos : ENNReal.ofReal (Real.exp (-K)) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      have h0 : ENNReal.ofReal (D z w) = 0 :=
        (mul_eq_zero.mp h).resolve_left hpos
      have hDzw : D z w = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp h0) (hDnn z w)
      exact hD.eq_of_eq_zero z w hDzw
    · -- triangle inequality, from `weylScaling_triangle` and finiteness
      intro x y z
      have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin x y, hfin y z⟩)
        (hD.weylScaling_triangle ξ f x y z)
      rw [ENNReal.toReal_add (hfin x y) (hfin y z)] at h
      exact h
    · -- topology: `e^{-K}`-comparison with `D`
      intro U
      constructor
      · intro hU z hz
        obtain ⟨ε, hε, hball⟩ := (hD.isOpen_iff U).mp hU z hz
        refine ⟨Real.exp (-K) * ε, mul_pos (Real.exp_pos _) hε, fun w hw => hball w ?_⟩
        have h1 : Real.exp (-K) * D z w < Real.exp (-K) * ε := lt_of_le_of_lt (hEge z w) hw
        exact lt_of_mul_lt_mul_left h1 (Real.exp_pos _).le
      · intro h
        refine (hD.isOpen_iff U).mpr fun z hz => ?_
        obtain ⟨ε, hε, hball⟩ := h z hz
        refine ⟨ε * Real.exp (-K), mul_pos hε (Real.exp_pos _), fun w hw => hball w ?_⟩
        have hexp : Real.exp K * (ε * Real.exp (-K)) = ε := by
          rw [Real.exp_neg]
          field_simp
        calc E z w ≤ Real.exp K * D z w := hEle z w
          _ < Real.exp K * (ε * Real.exp (-K)) := mul_lt_mul_of_pos_left hw (Real.exp_pos K)
          _ = ε := hexp
  exact hEmetric

end HarmonicBalls
