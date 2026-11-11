import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.Phase2.WeylCompositionOuterDerived
import HarmonicBalls.FirstPass.Phase2.AxiomsUnivDerived
import HarmonicBalls.Steps.Sec11.WholePlaneWeylShift
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Composition of Weyl scalings with a continuous inner weight (`WeylScalingCompositionFrozen`)

Derives `WeylScalingCompositionFrozen` (FirstPass/Frozen/S11d.lean:88) from the axioms of an LQG metric
(Gwynne-Miller 2021, Section 1.2, p. 6, axioms I and III, and Remark 1.5, p. 8).

Let `D` and `D'` be Euclidean length metrics and `g` a continuous function with `D' = e^{ξ g} · D` and
`D = e^{-ξ g} · D'` (axiom III for the fields `h` and `h + g`). Then for an arbitrary weight `L` (no regularity; here the
logarithmic singularity `-α₀ log |·|`), `e^{ξ L} · D' = e^{ξ (g + L)} · D`.

Proof (arclength substitution). Let `p` be parametrized by `D`-length on `[0, T]` and let `σ(t)` be the `D'`-length of
`p` on `[0, t]`. The cost bound for `D' = e^{ξ g} · D` gives `σ(b) - σ(a) ≤ ∫_a^b e^{ξ g(p)}`. The reparametrization
`q ∘ σ = p` of `p` by `D'`-length and the cost bound for `D = e^{-ξ g} · D'` give
`b - a ≤ ∫_{σ(a)}^{σ(b)} e^{-ξ g(q)}`. By continuity of `g ∘ p`, `σ` is differentiable with derivative `e^{ξ g(p)}`
and injective, and the change of variables `τ = σ(s)` turns `∫ w(q(τ)) dτ` into `∫ e^{ξ g(p(s))} w(p(s)) ds` for every
weight `w`. Both inequalities between the two infima follow, the second one by exchanging the roles of `D` and `D'`.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal
open FirstPassS11aa

/-- A monotone change of parameter does not decrease the length of a curve: if `q ∘ σ = p` on `[a, b]` with `σ`
monotone there, the `D`-length of `p` on `[a, b]` is at most that of `q` on `[σ a, σ b]`. -/
theorem curveLength_le_of_comp {D : ℂ → ℂ → ℝ} {p q : ℝ → ℂ} {σ : ℝ → ℝ} {a b : ℝ}
    (hσ : MonotoneOn σ (Icc a b)) (hqp : ∀ t ∈ Icc a b, q (σ t) = p t) :
    curveLength D p a b ≤ curveLength D q (σ a) (σ b) := by
  unfold curveLength
  refine iSup_le ?_
  rintro ⟨n, u, hu, hmem⟩
  have hab : a ≤ b := (hmem 0).1.trans (hmem 0).2
  have hmono : Monotone fun i => σ (u i) := fun i j hij => hσ (hmem i) (hmem j) (hu hij)
  have hmem' : ∀ i, σ (u i) ∈ Icc (σ a) (σ b) := fun i =>
    ⟨hσ ⟨le_rfl, hab⟩ (hmem i) (hmem i).1, hσ (hmem i) ⟨hab, le_rfl⟩ (hmem i).2⟩
  refine le_iSup_of_le ⟨n, ⟨fun i => σ (u i), hmono, hmem'⟩⟩ (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  show ENNReal.ofReal (D (p (u (i + 1))) (p (u i))) = ENNReal.ofReal (D (q (σ (u (i + 1)))) (q (σ (u i))))
  rw [hqp _ (hmem (i + 1)), hqp _ (hmem i)]

/-- Arclength substitution. Let `D`, `D'` be Euclidean length metrics with `D' = e^{ξ g} · D` and `D = e^{-ξ g} · D'`
for a continuous `g`. Every curve `p` parametrized by `D`-length has a reparametrization `q` by `D'`-length with the
same endpoints such that, for every weight `w`, `∫ w(q(τ)) dτ = ∫ e^{ξ g(p(s))} w(p(s)) ds`. -/
theorem IsEuclideanLengthMetric.exists_reparam_cost {D D' : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hD' : IsEuclideanLengthMetric D') {ξ : ℝ} {g : ℂ → ℝ} (hg : Continuous g)
    (h1 : ∀ u v, ENNReal.ofReal (D' u v) = weylScaling D ξ g u v)
    (h2 : ∀ u v, ENNReal.ofReal (D u v) = weylScaling D' ξ (fun z => -g z) u v)
    (w : ℂ → ℝ≥0∞) {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T) :
    ∃ (T' : ℝ) (q : ℝ → ℂ), IsLengthParametrized D' q T' ∧ q 0 = p 0 ∧ q T' = p T ∧
      ∫⁻ τ in Icc 0 T', w (q τ) =
        ∫⁻ s in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p s))) * w (p s) := by
  have hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤ := fun x y => by
    rw [← h1 x y]
    exact ENNReal.ofReal_ne_top
  have hfin' : ∀ x y, weylScaling D' ξ (fun z => -g z) x y ≠ ⊤ := fun x y => by
    rw [← h2 x y]
    exact ENNReal.ofReal_ne_top
  have hin : innerDist D ξ g = D' := by
    funext u v
    unfold innerDist
    rw [← h1 u v, ENNReal.toReal_ofReal (hD'.nonneg' u v)]
  have hin' : innerDist D' ξ (fun z => -g z) = D := by
    funext u v
    unfold innerDist
    rw [← h2 u v, ENNReal.toReal_ofReal (hD.nonneg' u v)]
  have hgo : ContinuousOn g {z | z ≠ 0} := hg.continuousOn
  have hφc : ContinuousOn (fun t => Real.exp (ξ * g (p t))) (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul hg)).comp_continuousOn hp.2.1
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hp.1⟩
  have hTT : T ∈ Icc 0 T := ⟨hp.1, le_rfl⟩
  obtain ⟨t1, -, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMaxOn ⟨0, h0T⟩ hφc
  obtain ⟨t0, -, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMinOn ⟨0, h0T⟩ hφc
  have hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' (g := fun _ => ENNReal.ofReal (Real.exp (ξ * g (p t1))))
      measurableSet_Icc fun t ht => ENNReal.ofReal_le_ofReal (isMaxOn_iff.mp hmax t ht))
    rw [setLIntegral_const, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- the `D'`-arclength of `p` and the reparametrization of `p` by it
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ → ℝ, ∀ t, σ t = (curveLength (innerDist D ξ g) p 0 t).toReal := ⟨_, fun _ => rfl⟩
  have hσfun : σ = fun t => (curveLength (innerDist D ξ g) p 0 t).toReal := funext hσ
  obtain ⟨q, hq, hq0, hqT, hqp⟩ := hD.exists_arclength_innerDist hgo hfin hp.1
    (hD.curveLength_ne_top_of_mem hfin hp hC hTT) (fun t ht => hD.innerDist_tendsto_of_cost hfin hp hC ht)
  rw [← hσ T] at hq hqT
  rw [hin] at hq
  have hqp' : ∀ t ∈ Icc (0 : ℝ) T, q (σ t) = p t := fun t ht => by
    rw [hσ t]
    exact hqp t ht
  have hsinc : ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T → a ≤ b → σ a ≤ σ b ∧
      ENNReal.ofReal (σ b - σ a) ≤ ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
    intro a b ha hb hab
    rw [hσ a, hσ b]
    exact hD.arc_sinc hgo hfin hp hC ha hb hab
  have hσc : ContinuousOn σ (Icc 0 T) := by
    rw [hσfun]
    exact hD.arc_continuousOn hgo hfin hp hC
  have hσnn : ∀ t, 0 ≤ σ t := fun t => by
    rw [hσ t]
    exact ENNReal.toReal_nonneg
  have hσ0 : σ 0 = 0 := by
    have hz : curveLength (innerDist D ξ g) p 0 0 = 0 := by
      unfold curveLength
      refine le_antisymm (iSup_le ?_) zero_le
      rintro ⟨n, u, hu, hmem⟩
      refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
      have e1 : u (i + 1) = 0 := le_antisymm (hmem (i + 1)).2 (hmem (i + 1)).1
      have e0 : u i = 0 := le_antisymm (hmem i).2 (hmem i).1
      show ENNReal.ofReal (innerDist D ξ g (p (u (i + 1))) (p (u i))) = 0
      rw [e1, e0, innerDist_self hD ξ g, ENNReal.ofReal_zero]
    rw [hσ 0, hz, ENNReal.toReal_zero]
  -- upper bound for the increments of `σ`
  have hupper : ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T → a ≤ b → ∀ M : ℝ,
      (∀ t ∈ Icc a b, Real.exp (ξ * g (p t)) ≤ M) → σ b - σ a ≤ M * (b - a) := by
    intro a b ha hb hab M hM
    have hM0 : 0 ≤ M := (Real.exp_pos _).le.trans (hM a ⟨le_rfl, hab⟩)
    have h := (hsinc a b ha hb hab).2
    have h' : ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≤ ENNReal.ofReal (M * (b - a)) := by
      calc ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t)))
          ≤ ∫⁻ _t in Icc a b, ENNReal.ofReal M :=
            setLIntegral_mono' measurableSet_Icc fun t ht => ENNReal.ofReal_le_ofReal (hM t ht)
        _ = ENNReal.ofReal M * ENNReal.ofReal (b - a) := by
            rw [setLIntegral_const, Real.volume_Icc]
        _ = ENNReal.ofReal (M * (b - a)) := (ENNReal.ofReal_mul hM0).symm
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM0 (sub_nonneg.mpr hab))).mp (h.trans h')
  -- lower bound for the increments of `σ`, from the inverse scaling
  have hlower : ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T → a ≤ b → ∀ m : ℝ, 0 < m →
      (∀ t ∈ Icc a b, m ≤ Real.exp (ξ * g (p t))) → m * (b - a) ≤ σ b - σ a := by
    intro a b ha hb hab m hm hmle
    have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha.1 hb.2
    have hσab : σ a ≤ σ b := (hsinc a b ha hb hab).1
    have hlen : curveLength D p a b = ENNReal.ofReal (b - a) := hp.2.2 a b ha.1 hab hb.2
    have hmonoab : MonotoneOn σ (Icc a b) := fun s hs t ht hst => (hsinc s t (hsub hs) (hsub ht) hst).1
    have e1 : curveLength D p a b ≤ curveLength D q (σ a) (σ b) :=
      curveLength_le_of_comp hmonoab fun t ht => hqp' t (hsub ht)
    have e2 : curveLength D q (σ a) (σ b) ≤
        ∫⁻ r in Icc (σ a) (σ b), ENNReal.ofReal (Real.exp (ξ * -g (q r))) := by
      have h := hD'.curveLength_innerDist_le_cost hfin' hq (u := σ a) (v := σ b) (hu := hσnn a)
        (hv := (hsinc b T hb hTT hb.2).1)
      rw [hin'] at h
      exact h
    have e3 : ∫⁻ r in Icc (σ a) (σ b), ENNReal.ofReal (Real.exp (ξ * -g (q r))) ≤
        ENNReal.ofReal (m⁻¹ * (σ b - σ a)) := by
      calc ∫⁻ r in Icc (σ a) (σ b), ENNReal.ofReal (Real.exp (ξ * -g (q r)))
          ≤ ∫⁻ _r in Icc (σ a) (σ b), ENNReal.ofReal m⁻¹ :=
            setLIntegral_mono' measurableSet_Icc fun r hr => by
              obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc hab (hσc.mono hsub) hr
              rw [hqp' t (hsub ht)]
              apply ENNReal.ofReal_le_ofReal
              rw [mul_neg, Real.exp_neg]
              exact inv_anti₀ hm (hmle t ht)
        _ = ENNReal.ofReal m⁻¹ * ENNReal.ofReal (σ b - σ a) := by
            rw [setLIntegral_const, Real.volume_Icc]
        _ = ENNReal.ofReal (m⁻¹ * (σ b - σ a)) := (ENNReal.ofReal_mul (inv_nonneg.mpr hm.le)).symm
    have e4 : ENNReal.ofReal (b - a) ≤ ENNReal.ofReal (m⁻¹ * (σ b - σ a)) := by
      rw [← hlen]
      exact e1.trans (e2.trans e3)
    have e5 : b - a ≤ m⁻¹ * (σ b - σ a) :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (inv_nonneg.mpr hm.le) (sub_nonneg.mpr hσab))).mp e4
    have e6 := mul_le_mul_of_nonneg_left e5 hm.le
    rwa [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul] at e6
  -- two-sided estimate on an interval where `e^{ξ g ∘ p}` is within `e` of `c`
  have hkey : ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T → a ≤ b → ∀ c e : ℝ, 0 < c - e →
      (∀ t ∈ Icc a b, |Real.exp (ξ * g (p t)) - c| ≤ e) → |σ b - σ a - (b - a) * c| ≤ e * (b - a) := by
    intro a b ha hb hab c e hce hclose
    have hU := hupper a b ha hb hab (c + e) fun t ht => by
      have := (abs_le.mp (hclose t ht)).2
      linarith
    have hL := hlower a b ha hb hab (c - e) hce fun t ht => by
      have := (abs_le.mp (hclose t ht)).1
      linarith
    rw [abs_le]
    constructor <;> nlinarith
  -- `σ` is differentiable with derivative `e^{ξ g ∘ p}`
  have hderiv : ∀ x ∈ Icc (0 : ℝ) T, HasDerivWithinAt σ (Real.exp (ξ * g (p x))) (Icc 0 T) x := by
    intro x hx
    rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro ε hε
    have hpos : 0 < Real.exp (ξ * g (p x)) := Real.exp_pos _
    set e : ℝ := min ε (Real.exp (ξ * g (p x)) / 2) with he
    have he0 : 0 < e := lt_min hε (half_pos hpos)
    have heε : e ≤ ε := min_le_left _ _
    have hec : 0 < Real.exp (ξ * g (p x)) - e := by
      have : e ≤ Real.exp (ξ * g (p x)) / 2 := min_le_right _ _
      linarith
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.mp (hφc x hx) e he0
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hδ)] with y hy hyδ
    have hyδ' : |y - x| < δ := by
      rw [← Real.dist_eq]
      exact hyδ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
    rcases le_total x y with hxy | hyx
    · have hclose : ∀ t ∈ Icc x y, |Real.exp (ξ * g (p t)) - Real.exp (ξ * g (p x))| ≤ e := fun t ht => by
        have htd : dist t x < δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
          rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at hyδ'
          linarith [ht.2]
        have := hδc ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩ htd
        rw [Real.dist_eq] at this
        exact this.le
      have hk := hkey x y hx hy hxy _ e hec hclose
      rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact hk.trans (mul_le_mul_of_nonneg_right heε (sub_nonneg.mpr hxy))
    · have hclose : ∀ t ∈ Icc y x, |Real.exp (ξ * g (p t)) - Real.exp (ξ * g (p x))| ≤ e := fun t ht => by
        have htd : dist t x < δ := by
          rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.2)]
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hyx)] at hyδ'
          linarith [ht.1]
        have := hδc ⟨hy.1.trans ht.1, ht.2.trans hx.2⟩ htd
        rw [Real.dist_eq] at this
        exact this.le
      have hk := hkey y x hy hx hyx _ e hec hclose
      rw [abs_sub_comm y x, abs_of_nonneg (sub_nonneg.mpr hyx)]
      have hrew : σ y - σ x - (y - x) * Real.exp (ξ * g (p x)) =
          -(σ x - σ y - (x - y) * Real.exp (ξ * g (p x))) := by ring
      rw [hrew, abs_neg]
      exact hk.trans (mul_le_mul_of_nonneg_right heε (sub_nonneg.mpr hyx))
  -- `σ` is injective and maps `[0, T]` onto `[0, σ T]`
  have hstrict : ∀ a b, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T → a < b → σ a < σ b := by
    intro a b ha hb hab
    have h := hlower a b ha hb hab.le _ (Real.exp_pos (ξ * g (p t0))) fun t ht =>
      isMinOn_iff.mp hmin t ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
    have hpos : 0 < Real.exp (ξ * g (p t0)) * (b - a) := mul_pos (Real.exp_pos _) (sub_pos.mpr hab)
    linarith
  have hinj : InjOn σ (Icc 0 T) := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hstrict a b ha hb h).ne hab
    · exact (hstrict b a hb ha h).ne' hab
  have himage : σ '' Icc 0 T = Icc 0 (σ T) := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨hσnn t, (hsinc t T ht hTT ht.2).1⟩
    · have h := intermediate_value_Icc hp.1 hσc
      rwa [hσ0] at h
  refine ⟨σ T, q, hq, hq0, hqT, ?_⟩
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hderiv hinj (fun τ => w (q τ))
  rw [himage] at hcov
  rw [hcov]
  refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  show ENNReal.ofReal |Real.exp (ξ * g (p s))| * w (q (σ s)) = ENNReal.ofReal (Real.exp (ξ * g (p s))) * w (p s)
  rw [abs_of_pos (Real.exp_pos _), hqp' s hs]

/-- Composition of Weyl scalings with a continuous inner weight and an arbitrary outer weight: if `D`, `D'` are
Euclidean length metrics with `D' = e^{ξ g} · D` and `D = e^{-ξ g} · D'` for a continuous `g`, then
`e^{ξ L} · D' = e^{ξ (g + L)} · D` for every `L`. -/
theorem IsEuclideanLengthMetric.weylScaling_eq_of_mutual {D D' : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hD' : IsEuclideanLengthMetric D') {ξ : ℝ} {g : ℂ → ℝ} (hg : Continuous g)
    (h1 : ∀ u v, ENNReal.ofReal (D' u v) = weylScaling D ξ g u v)
    (h2 : ∀ u v, ENNReal.ofReal (D u v) = weylScaling D' ξ (fun z => -g z) u v)
    (L : ℂ → ℝ) (x y : ℂ) :
    weylScaling D' ξ L x y = weylScaling D ξ (fun z => g z + L z) x y := by
  apply le_antisymm
  · show weylScaling D' ξ L x y ≤ ⨅ (T : ℝ) (p : ℝ → ℂ) (_ : IsLengthParametrized D p T)
      (_ : p 0 = x) (_ : p T = y), ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + L (p t))))
    refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 => le_iInf fun hT => ?_
    obtain ⟨T', q, hq, hq0, hqT, hint⟩ := hD.exists_reparam_cost hD' hg h1 h2
      (fun z => ENNReal.ofReal (Real.exp (ξ * L z))) hp
    have hle : weylScaling D' ξ L x y ≤ ∫⁻ τ in Icc 0 T', ENNReal.ofReal (Real.exp (ξ * L (q τ))) :=
      iInf_le_of_le T' (iInf_le_of_le q (iInf_le_of_le hq (iInf_le_of_le (hq0.trans h0)
        (iInf_le_of_le (hqT.trans hT) le_rfl))))
    refine hle.trans (le_of_eq ?_)
    rw [hint]
    refine setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    show ENNReal.ofReal (Real.exp (ξ * g (p s))) * ENNReal.ofReal (Real.exp (ξ * L (p s))) =
      ENNReal.ofReal (Real.exp (ξ * (g (p s) + L (p s))))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_add]
  · show weylScaling D ξ (fun z => g z + L z) x y ≤ ⨅ (T : ℝ) (q : ℝ → ℂ) (_ : IsLengthParametrized D' q T)
      (_ : q 0 = x) (_ : q T = y), ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * L (q t)))
    refine le_iInf fun T => le_iInf fun q => le_iInf fun hq => le_iInf fun h0 => le_iInf fun hT => ?_
    have h1' : ∀ u v, ENNReal.ofReal (D' u v) = weylScaling D ξ (fun z => -(fun z => -g z) z) u v := by
      intro u v
      simpa only [neg_neg] using h1 u v
    obtain ⟨T', p, hp, hp0, hpT, hint⟩ := hD'.exists_reparam_cost hD hg.neg h2 h1'
      (fun z => ENNReal.ofReal (Real.exp (ξ * (g z + L z)))) hq
    have hle : weylScaling D ξ (fun z => g z + L z) x y ≤
        ∫⁻ τ in Icc 0 T', ENNReal.ofReal (Real.exp (ξ * (g (p τ) + L (p τ)))) :=
      iInf_le_of_le T' (iInf_le_of_le p (iInf_le_of_le hp (iInf_le_of_le (hp0.trans h0)
        (iInf_le_of_le (hpT.trans hT) le_rfl))))
    refine hle.trans (le_of_eq ?_)
    rw [hint]
    refine setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    show ENNReal.ofReal (Real.exp (ξ * -g (q s))) * ENNReal.ofReal (Real.exp (ξ * (g (q s) + L (q s)))) =
      ENNReal.ofReal (Real.exp (ξ * L (q s)))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring

/-- Derivation of `WeylScalingCompositionFrozen` (FirstPass/Frozen/S11d.lean:88): for a whole-plane GFF `h^ℂ`, an LQG
metric `𝔇` and a continuous `g`, almost surely the metric of `h^ℂ + g - α₀ log |·|` is the Weyl scaling of
`𝔇(h^ℂ)` by `g - α₀ log |·|`. Axioms I and III are used for the fields `h^ℂ` and `h^ℂ + g`. -/
theorem weylScalingCompositionFrozen_holds : WeylScalingCompositionFrozen.{u} := by
  intro γ ξ α₀ Ω _ P hC hcirc hGFF _ _ _ 𝔇 h𝔇 g hg
  have hA := lqgMetricSatisfiesAxiomsUniv_derived.{u} γ ξ 𝔇 h𝔇 Ω P hC hcirc (fun _ _ => (0 : ℝ))
    hGFF (fun _ => continuous_const) (fun _ => measurable_const)
  have hB := lqgMetricSatisfiesAxiomsUniv_derived.{u} γ ξ 𝔇 h𝔇 Ω P hC hcirc (fun _ => g)
    hGFF (fun _ => hg) (fun _ => measurable_const)
  filter_upwards [hA.ae_isEuclideanLengthMetric, hA.ae_weylScaling, hB.ae_isEuclideanLengthMetric,
    hB.ae_weylScaling] with ω hI hIII hI' hIII' x y
  have h0 : addFunPairing (hC ω) (fun _ => (0 : ℝ)) = hC ω := addFunPairing_zero_fun (hC ω)
  have hI0 : IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    have h : IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) (fun _ => (0 : ℝ)))) := hI
    rwa [h0] at h
  have h1 : ∀ u v, ENNReal.ofReal (𝔇 (addFunPairing (hC ω) g) u v) = weylScaling (𝔇 (hC ω)) ξ g u v := by
    intro u v
    have h := hIII g hg u v
    have h' : ENNReal.ofReal (𝔇 (addFunPairing (addFunPairing (hC ω) (fun _ => (0 : ℝ))) g) u v) =
        weylScaling (𝔇 (addFunPairing (hC ω) (fun _ => (0 : ℝ)))) ξ g u v := h
    rwa [h0] at h'
  have h2 : ∀ u v, ENNReal.ofReal (𝔇 (hC ω) u v) =
      weylScaling (𝔇 (addFunPairing (hC ω) g)) ξ (fun z => -g z) u v := by
    intro u v
    have h := hIII' (fun z => -g z) hg.neg u v
    have h' : ENNReal.ofReal (𝔇 (addFunPairing (addFunPairing (hC ω) g) (fun z => -g z)) u v) =
        weylScaling (𝔇 (addFunPairing (hC ω) g)) ξ (fun z => -g z) u v := h
    rwa [addFunPairing_neg_cancel] at h'
  have hmain := hI0.weylScaling_eq_of_mutual hI' hg h1 h2 (fun z => -α₀ * Real.log ‖z‖) x y
  have hfun : (fun z : ℂ => g z - α₀ * Real.log ‖z‖) = fun z => g z + -α₀ * Real.log ‖z‖ := by
    funext z
    ring
  rw [hfun]
  exact hmain

end HarmonicBalls
