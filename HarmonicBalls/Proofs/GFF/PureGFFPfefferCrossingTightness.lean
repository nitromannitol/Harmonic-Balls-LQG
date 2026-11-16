import HarmonicBalls.Proofs.GFF.MetricAnnulusScaleLaw
import HarmonicBalls.Proofs.Metric.CompactAnnulusSeparation
import HarmonicBalls.Proposed.PfefferMetricScaling
import HarmonicBalls.Steps.Sec11.ApproximatePaths
import HarmonicBalls.Steps.Sec11.InternalMetricPaths

/-! # Crossing tightness for the pure whole-plane GFF (Pfeffer, Definition 1.6, Axiom V)

Sources: Pfeffer, *Weak Liouville quantum gravity metrics with matter central charge up to 25*, arXiv:2104.04020v3,
Definition 1.6, Axiom V; Gwynne–Miller, *Existence and uniqueness of the Liouville quantum gravity metric for
`γ ∈ (0, 2)`*, arXiv:1905.00383v3, (1.13) and (1.15).

Setting. `𝔇` is a `γ`-LQG metric with Weyl exponent `ξ` (`IsLQGMetric γ ξ 𝔇`) and `h` is a whole-plane GFF
(`IsWholePlaneGFF P hC hcirc`). The field of Axiom V is `h^ℂ + f` with `f = 0`, and the scaling constants are
`c_r = r^{ξQ}` with `Q = lqgQ γ`. By (1.15) (coordinate change and Weyl scaling, `zeroCharge_scale_ae`), for each
`r > 0` the metric `c_r⁻¹ e^{-ξ h_r(0)} D_h(r ·, r ·)` is almost surely the metric of the whole-plane GFF
`h(r ·) - h_r(0)`, whose law is that of `h`.

Results.
* `pureGFF_pfefferAcross_tight`: tightness and reciprocal tightness over `r > 0` of the normalized distance across
  `A(r z₀; r a, r b)`, restated from `normalizedAcross_tight`.
* `pureGFF_pfefferAround_tight`: the same for the normalized distance around the annulus (`pfefferAround`).
* `IsLQGMetric.pureGFF_pfefferAxiomVScale`: `PfefferAxiomVScale` for `f = 0` and `c_r = r^{ξQ}`, that is positivity of
  `c_r`, (b) for every annulus, and the bound (1.7).

Distance around an annulus. It is bounded below by the distance between the radial segments `{z₀ + s : a ≤ s ≤ b}`
and `{z₀ - s : a ≤ s ≤ b}`, which every separating closed path meets (`setPairInf_le_pfefferAround`). It is bounded
above by `∑_{j < k} D(w_j, w_{j+1})` for `k` equally spaced points `w_j` on the middle circle, whenever each step is
shorter than the distance from `w_j` to the circle `∂B_δ(w_j)` (`ChainGood`, `pfefferAround_le_chainSum`):
near-geodesics between consecutive points then stay in the disks `B_δ(w_j)`, and their concatenation is a closed path in
the annulus with winding number one around `z₀`, so it separates the two boundary circles. Winding numbers are
increments of continuous logarithms (`windIncr`), obtained from the covering map `exp : ℂ → ℂ \ {0}` and its homotopy
lifting property. Both bounds are measurable functions of the field through countable dense subsets, they scale exactly
under `z ↦ r z`, and almost surely some number of points is good (`exists_chainGood`).

Scope. Only the pure field (`f = 0`) with the scaling `c_r = r^{ξQ}` is treated. Nothing here concerns `h^ℂ + f` for
nonzero `f` or the class `IsPfefferWeakLQGMetric`.

Credit: the whole-plane GFF `h^ℂ` and its affine invariance (`wholePlaneGFFAffineInvariance_proved`) are due to
Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology unitInterval

namespace PureGFFCrossing

/-! ### Continuous logarithms along paths -/

/-- Two continuous logarithms of the same nonvanishing function on `[0, 1]` have the same increment. -/
theorem increment_eq_of_exp_eq {L₁ L₂ : I → ℂ} (h₁ : Continuous L₁) (h₂ : Continuous L₂)
    (h : ∀ t, Complex.exp (L₁ t) = Complex.exp (L₂ t)) : L₁ 1 - L₁ 0 = L₂ 1 - L₂ 0 := by
  have hc := Complex.isCoveringMap_exp.const_of_comp (g := fun t : I => L₁ t - L₂ t) (h₁.sub h₂)
    (fun t t' => by
      apply Subtype.ext
      show Complex.exp (L₁ t - L₂ t) = Complex.exp (L₁ t' - L₂ t')
      rw [Complex.exp_sub, Complex.exp_sub, h, h, div_self (Complex.exp_ne_zero _),
        div_self (Complex.exp_ne_zero _)]) 1 0
  linear_combination hc

/-- Every continuous nonvanishing function on `[0, 1]` has a continuous logarithm. -/
theorem exists_continuous_exp_eq (q : C(I, {z : ℂ // z ≠ 0})) :
    ∃ L : C(I, ℂ), ∀ t, Complex.exp (L t) = (q t : ℂ) := by
  obtain ⟨L, hL, -⟩ := Complex.isCoveringMap_exp.exists_path_lifts q (Complex.log (q 0))
    (Subtype.ext (Complex.exp_log (q 0).2).symm)
  exact ⟨L, fun t => congrArg Subtype.val (congrFun hL t)⟩

/-- The function `t ↦ γ t - c` of a path `γ` avoiding `c`, as a map into `ℂ \ {0}`. -/
def pathSub {x y : ℂ} (γ : Path x y) (c : ℂ) (hc : ∀ t, γ t ≠ c) : C(I, {z : ℂ // z ≠ 0}) :=
  ⟨fun t => ⟨γ t - c, sub_ne_zero.2 (hc t)⟩, (γ.continuous.sub continuous_const).subtype_mk _⟩

open Classical in
/-- The increment `L 1 - L 0` of a continuous logarithm `L` of `t ↦ γ t - c` along a path `γ` avoiding `c`, and `0`
if `γ` meets `c`. For a closed path it is `2πi` times the winding number of `γ` around `c`. -/
noncomputable def windIncr {x y : ℂ} (γ : Path x y) (c : ℂ) : ℂ :=
  if hc : ∀ t, γ t ≠ c then
    (exists_continuous_exp_eq (pathSub γ c hc)).choose 1 - (exists_continuous_exp_eq (pathSub γ c hc)).choose 0
  else 0

theorem windIncr_eq {x y : ℂ} {γ : Path x y} {c : ℂ} (hc : ∀ t, γ t ≠ c) {L : I → ℂ} (hL : Continuous L)
    (hexp : ∀ t, Complex.exp (L t) = γ t - c) : windIncr γ c = L 1 - L 0 := by
  rw [windIncr, dite_eq_left hc]
  exact increment_eq_of_exp_eq (exists_continuous_exp_eq (pathSub γ c hc)).choose.continuous hL
    (fun t => ((exists_continuous_exp_eq (pathSub γ c hc)).choose_spec t).trans (hexp t).symm)

/-- On a path along which `(γ t - c)/u` stays in the right half-plane, the increment is given by the principal
logarithm. -/
theorem windIncr_of_re_pos {x y : ℂ} (γ : Path x y) {c u : ℂ} (hu : u ≠ 0)
    (h : ∀ t, 0 < ((γ t - c) / u).re) :
    windIncr γ c = Complex.log ((y - c) / u) - Complex.log ((x - c) / u) := by
  have hne : ∀ t, (γ t - c) / u ≠ 0 := fun t h0 => by
    have := h t
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hc : ∀ t, γ t ≠ c := fun t h0 => hne t (by rw [h0, sub_self, zero_div])
  have hcont : Continuous fun t => Complex.log ((γ t - c) / u) + Complex.log u :=
    (((γ.continuous.sub continuous_const).div_const u).clog
      (fun t => Complex.mem_slitPlane_iff.2 (Or.inl (h t)))).add continuous_const
  have hexp : ∀ t, Complex.exp (Complex.log ((γ t - c) / u) + Complex.log u) = γ t - c := fun t => by
    rw [Complex.exp_add, Complex.exp_log (hne t), Complex.exp_log hu, div_mul_cancel₀ _ hu]
  rw [windIncr_eq hc hcont hexp, γ.source, γ.target]
  ring

theorem windIncr_refl (x c : ℂ) (hc : x ≠ c) : windIncr (Path.refl x) c = 0 := by
  have hexp : ∀ t, Complex.exp ((fun _ : I => Complex.log (x - c)) t) = Path.refl x t - c := fun t => by
    simp [Complex.exp_log (sub_ne_zero.2 hc)]
  rw [windIncr_eq (fun _ => hc) continuous_const hexp, sub_self]

theorem windIncr_cast {x y x' y' : ℂ} (γ : Path x y) (hx : x' = x) (hy : y' = y) (c : ℂ)
    (hc : ∀ t, γ t ≠ c) : windIncr (γ.cast hx hy) c = windIncr γ c := by
  obtain ⟨L, hL⟩ := exists_continuous_exp_eq (pathSub γ c hc)
  rw [windIncr_eq hc L.continuous hL, windIncr_eq (γ := γ.cast hx hy) (fun t => hc t) L.continuous hL]

theorem windIncr_trans {x y z : ℂ} (γ₁ : Path x y) (γ₂ : Path y z) {c : ℂ} (h₁ : ∀ t, γ₁ t ≠ c)
    (h₂ : ∀ t, γ₂ t ≠ c) :
    windIncr (γ₁.trans γ₂) c = windIncr γ₁ c + windIncr γ₂ c := by
  obtain ⟨L₁, hL₁⟩ := exists_continuous_exp_eq (pathSub γ₁ c h₁)
  obtain ⟨L₂, hL₂⟩ := exists_continuous_exp_eq (pathSub γ₂ c h₂)
  have hyc : y - c ≠ 0 := sub_ne_zero.2 (by simpa using h₂ 0)
  have hy : Complex.exp (L₁ 1 - L₂ 0) = 1 := by
    rw [Complex.exp_sub, hL₁, hL₂]
    show (γ₁ 1 - c) / (γ₂ 0 - c) = 1
    rw [γ₁.target, γ₂.source]
    exact div_self hyc
  let P₁ : Path (L₁ 0) (L₁ 1) := ⟨L₁, rfl, rfl⟩
  let P₂ : Path (L₁ 1) (L₂ 1 + (L₁ 1 - L₂ 0)) :=
    ⟨⟨fun t => L₂ t + (L₁ 1 - L₂ 0), L₂.continuous.add continuous_const⟩, by simp, rfl⟩
  have h12 : ∀ t, (γ₁.trans γ₂) t ≠ c := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact h₁ _
    · exact h₂ _
  have hexp : ∀ t, Complex.exp ((P₁.trans P₂) t) = (γ₁.trans γ₂) t - c := by
    intro t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hL₁ _
    · show Complex.exp (L₂ _ + (L₁ 1 - L₂ 0)) = γ₂ _ - c
      rw [Complex.exp_add, hy, mul_one]
      exact hL₂ _
  rw [windIncr_eq h₁ L₁.continuous hL₁, windIncr_eq h₂ L₂.continuous hL₂,
    windIncr_eq h12 (P₁.trans P₂).continuous hexp, Path.source, Path.target]
  ring

/-- Homotopy invariance: moving the base point along a path that avoids a closed path does not change the
increment along the closed path. -/
theorem windIncr_eq_of_path {z c c' : ℂ} (Λ : Path z z) (β : Path c c') (h : ∀ s t, Λ s ≠ β t) :
    windIncr Λ c = windIncr Λ c' := by
  let H : C(I × I, {w : ℂ // w ≠ 0}) :=
    ⟨fun p => ⟨Λ p.1 - β p.2, sub_ne_zero.2 (h p.1 p.2)⟩,
      ((Λ.continuous.comp continuous_fst).sub (β.continuous.comp continuous_snd)).subtype_mk _⟩
  let q₀ : C(I, {w : ℂ // w ≠ 0}) :=
    ⟨fun t => H (0, t), H.continuous.comp (Continuous.prodMk continuous_const continuous_id)⟩
  obtain ⟨f, hf⟩ := exists_continuous_exp_eq q₀
  have H0 : ∀ t, H (0, t) = (⟨Complex.exp (f t), Complex.exp_ne_zero _⟩ : {w : ℂ // w ≠ 0}) :=
    fun t => Subtype.ext (hf t).symm
  let G := Complex.isCoveringMap_exp.liftHomotopy H f H0
  have hGl : ∀ s t, Complex.exp (G (s, t)) = Λ s - β t := fun s t =>
    congrArg Subtype.val (congrFun (Complex.isCoveringMap_exp.liftHomotopy_lifts H f H0) (s, t))
  have hw : ∀ t, windIncr Λ (β t) = G (1, t) - G (0, t) := fun t =>
    windIncr_eq (fun s => h s t) (G.continuous.comp (Continuous.prodMk continuous_id continuous_const))
      (fun s => hGl s t)
  have hz : ∀ t, z - β t ≠ 0 := fun t => sub_ne_zero.2 (by simpa using h 0 t)
  have hconst := Complex.isCoveringMap_exp.const_of_comp (g := fun t : I => G (1, t) - G (0, t))
    ((G.continuous.comp (Continuous.prodMk continuous_const continuous_id)).sub
      (G.continuous.comp (Continuous.prodMk continuous_const continuous_id)))
    (fun t t' => by
      apply Subtype.ext
      show Complex.exp (G (1, t) - G (0, t)) = Complex.exp (G (1, t') - G (0, t'))
      rw [Complex.exp_sub, Complex.exp_sub, hGl, hGl, hGl, hGl, Λ.source, Λ.target, div_self (hz t),
        div_self (hz t')]) 0 1
  have h0 := hw 0
  have h1 := hw 1
  rw [β.source] at h0
  rw [β.target] at h1
  rw [h0, h1]
  exact hconst

/-- If `|w - p| < |p - c|`, then `(w - c)/(p - c)` lies in the right half-plane. -/
theorem re_div_pos_of_norm_lt {w p c : ℂ} (h : ‖w - p‖ < ‖p - c‖) : 0 < ((w - c) / (p - c)).re := by
  have hpc : p - c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h
    exact absurd h (not_lt.2 (norm_nonneg _))
  have heq : (w - c) / (p - c) = 1 + (w - p) / (p - c) := by
    field_simp
    ring
  rw [heq, Complex.add_re, Complex.one_re]
  have h1 : ‖(w - p) / (p - c)‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.2 hpc)]
    exact h
  have h2 := Complex.abs_re_le_norm ((w - p) / (p - c))
  linarith [neg_abs_le ((w - p) / (p - c)).re]

/-! ### Closed paths separating the boundary circles of an annulus -/

/-- A closed path in `{a < |w - z₀| < b}` with nonzero increment around `z₀` separates the circles `∂B_a(z₀)` and
`∂B_b(z₀)`. -/
theorem separates_of_windIncr_ne_zero {z z₀ : ℂ} {a b : ℝ} (Λ : Path z z)
    (hin : ∀ s, a < ‖Λ s - z₀‖) (hout : ∀ s, ‖Λ s - z₀‖ < b) (hw : windIncr Λ z₀ ≠ 0) :
    PfefferSeparates Λ z₀ a b := by
  intro x y γ hx hy
  by_contra hne
  simp only [not_exists] at hne
  have hxn : ‖x - z₀‖ = a := by rw [← Complex.dist_eq]; exact Metric.mem_sphere.1 hx
  have hyn : ‖y - z₀‖ = b := by rw [← Complex.dist_eq]; exact Metric.mem_sphere.1 hy
  let seg : Path z₀ x :=
    ⟨⟨fun t => z₀ + ((t : ℝ) : ℂ) * (x - z₀), by fun_prop⟩, by simp, by simp⟩
  have hseg : ∀ t, ‖seg t - z₀‖ ≤ a := by
    intro t
    show ‖z₀ + ((t : ℝ) : ℂ) * (x - z₀) - z₀‖ ≤ a
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg t.2.1, hxn]
    have ha : 0 ≤ a := hxn ▸ norm_nonneg _
    nlinarith [t.2.2]
  have havoid : ∀ s t, Λ s ≠ (seg.trans γ) t := by
    intro s t heq
    have hmem : (seg.trans γ) t ∈ range seg ∪ range γ := by
      rw [← Path.trans_range]
      exact mem_range_self t
    rcases hmem with ⟨t', ht'⟩ | ⟨t', ht'⟩
    · have h1 := hin s
      rw [heq, ← ht'] at h1
      linarith [hseg t']
    · exact hne t' ⟨s, by rw [heq, ← ht']⟩
  have hu : z₀ - y ≠ 0 := by
    intro h0
    have : ‖y - z₀‖ = 0 := by rw [norm_sub_rev, h0, norm_zero]
    have := hout 0
    linarith [norm_nonneg (Λ 0 - z₀)]
  have hzero : windIncr Λ y = 0 := by
    rw [windIncr_of_re_pos Λ hu (fun s => re_div_pos_of_norm_lt ?_), sub_self]
    rw [norm_sub_rev z₀ y, hyn]
    exact hout s
  exact hw (by rw [windIncr_eq_of_path Λ (seg.trans γ) havoid, hzero])

/-- The point `z₀ + ρ e^{2πi j/k}`, the `j`-th of `k` equally spaced points on the circle `∂B_ρ(z₀)`. -/
noncomputable def circlePoint (z₀ : ℂ) (ρ : ℝ) (k j : ℕ) : ℂ :=
  z₀ + ρ * Complex.exp (((2 * Real.pi * j / k : ℝ) : ℂ) * Complex.I)

theorem norm_circlePoint_sub (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (k j : ℕ) : ‖circlePoint z₀ ρ k j - z₀‖ = ρ := by
  rw [circlePoint, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hρ]

theorem circlePoint_ratio (z₀ : ℂ) {ρ : ℝ} (hρ : ρ ≠ 0) (k j : ℕ) :
    (circlePoint z₀ ρ k (j + 1) - z₀) / (circlePoint z₀ ρ k j - z₀) =
      Complex.exp (((2 * Real.pi / k : ℝ) : ℂ) * Complex.I) := by
  simp only [circlePoint, add_sub_cancel_left]
  rw [mul_div_mul_left _ _ (Complex.ofReal_ne_zero.2 hρ), ← Complex.exp_sub]
  congr 1
  push_cast
  ring

theorem circlePoint_self (z₀ : ℂ) (ρ : ℝ) {k : ℕ} (hk : k ≠ 0) : circlePoint z₀ ρ k k = circlePoint z₀ ρ k 0 := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  simp only [circlePoint, Nat.cast_zero, mul_zero, zero_div, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [mul_div_assoc, div_self hk', mul_one]
  push_cast
  rw [Complex.exp_two_pi_mul_I]

theorem circlePoint_smul {r : ℝ} (z₀ : ℂ) (ρ : ℝ) (k j : ℕ) :
    circlePoint ((r : ℂ) * z₀) (r * ρ) k j = (r : ℂ) * circlePoint z₀ ρ k j := by
  simp only [circlePoint]
  push_cast
  ring

/-! ### Concatenated paths -/

/-- The concatenation of the paths `p 0, ..., p (j - 1)`, a path from `w 0` to `w j`. -/
noncomputable def chainPath (w : ℕ → ℂ) (p : ∀ j, Path (w j) (w (j + 1))) : ∀ j, Path (w 0) (w j)
  | 0 => Path.refl (w 0)
  | j + 1 => (chainPath w p j).trans (p j)

theorem chainPath_mem {w : ℕ → ℂ} {p : ∀ j, Path (w j) (w (j + 1))} {R : Set ℂ} (h0 : w 0 ∈ R) :
    ∀ n, (∀ j < n, ∀ t, p j t ∈ R) → ∀ t, chainPath w p n t ∈ R
  | 0, _, t => by simpa [chainPath] using h0
  | n + 1, hp, t => by
    have hmem : chainPath w p (n + 1) t ∈ range (chainPath w p n) ∪ range (p n) := by
      rw [chainPath, ← Path.trans_range]
      exact mem_range_self t
    rcases hmem with ⟨t', ht'⟩ | ⟨t', ht'⟩
    · rw [← ht']
      exact chainPath_mem h0 n (fun j hj => hp j (Nat.lt_succ_of_lt hj)) t'
    · rw [← ht']
      exact hp n (Nat.lt_succ_self n) t'

theorem windIncr_chainPath {w : ℕ → ℂ} {p : ∀ j, Path (w j) (w (j + 1))} {c : ℂ} (h0 : w 0 ≠ c) :
    ∀ n, (∀ j < n, ∀ t, p j t ≠ c) →
      windIncr (chainPath w p n) c = ∑ j ∈ Finset.range n, windIncr (p j) c
  | 0, _ => by simpa [chainPath] using windIncr_refl (w 0) c h0
  | n + 1, hp => by
    have hn : ∀ j < n, ∀ t, p j t ≠ c := fun j hj => hp j (Nat.lt_succ_of_lt hj)
    have hch : ∀ t, chainPath w p n t ≠ c :=
      chainPath_mem (R := {c}ᶜ) h0 n hn
    rw [chainPath, windIncr_trans _ _ hch (hp n (Nat.lt_succ_self n)), windIncr_chainPath h0 n hn,
      Finset.sum_range_succ]

theorem pathLength_refl {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x : ℂ) :
    pathLength D (Path.refl x) = 0 := by
  simp [pathLength, curveLength, Path.refl_extend, hD.self_eq_zero]

theorem pathLength_chainPath_le {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {w : ℕ → ℂ}
    (p : ∀ j, Path (w j) (w (j + 1))) :
    ∀ n, pathLength D (chainPath w p n) ≤ ∑ j ∈ Finset.range n, pathLength D (p j)
  | 0 => by simp [chainPath, pathLength_refl hD]
  | n + 1 => by
    rw [chainPath, Finset.sum_range_succ]
    exact (hD.pathLength_trans_le _ _).trans (by gcongr; exact pathLength_chainPath_le hD p n)

/-! ### Lengths of paths -/

/-- The `D`-length of a path dominates `D(p t, p s)` for `s ≤ t`. -/
theorem ofReal_le_pathLength_of_le (D : ℂ → ℂ → ℝ) {w w' : ℂ} (p : Path w w') {s t : I} (hst : s ≤ t) :
    ENNReal.ofReal (D (p t) (p s)) ≤ pathLength D p := by
  let u : ℕ → ℝ := fun i => if i = 0 then (s : ℝ) else t
  have hu : Monotone u := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [u, hi, hj]
      · simp only [u, hi, hj, ↓reduceIte]
        exact hst
    · have hj : j ≠ 0 := by omega
      simp [u, hi, hj]
  have hmem : ∀ i, u i ∈ Icc (0 : ℝ) 1 := fun i => by
    by_cases hi : i = 0
    · simp only [u, hi, ↓reduceIte]
      exact s.2
    · simp only [u, hi, ↓reduceIte]
      exact t.2
  unfold pathLength curveLength
  refine le_trans (le_of_eq ?_) (le_iSup (fun q : ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0 : ℝ) 1 } =>
    ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D (p.extend (q.2.1 (i + 1))) (p.extend (q.2.1 i))))
      (1, ⟨u, hu, hmem⟩))
  simp [u]

/-- A path from `w` whose `D`-length is smaller than the `D`-distance from `w` to every point of the circle
`∂B_δ(w)` stays in the open disk `B_δ(w)`. -/
theorem mem_ball_of_pathLength_lt {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {w w' : ℂ} (p : Path w w')
    {δ : ℝ} (hδ : 0 < δ) (h : ∀ y ∈ Metric.sphere w δ, pathLength D p < ENNReal.ofReal (D w y)) :
    ∀ t, p t ∈ Metric.ball w δ := by
  have hsub : range p ⊆ Metric.ball w δ ∪ (Metric.closedBall w δ)ᶜ := by
    rintro _ ⟨t, rfl⟩
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not, Metric.mem_ball, Metric.mem_closedBall] at hcon
    have hsph : p t ∈ Metric.sphere w δ := Metric.mem_sphere.2 (le_antisymm hcon.2 (not_lt.1 hcon.1))
    have hle : ENNReal.ofReal (D w (p t)) ≤ pathLength D p := by
      have := ofReal_le_pathLength_of_le D p (show (0 : I) ≤ t from t.2.1)
      rwa [p.source, hD.symm] at this
    exact lt_irrefl _ ((h _ hsph).trans_le hle)
  intro t
  exact (isPreconnected_range p.continuous).subset_left_of_subset_union Metric.isOpen_ball
    Metric.isClosed_closedBall.isOpen_compl (Disjoint.mono_left Metric.ball_subset_closedBall disjoint_compl_right)
    hsub ⟨w, ⟨0, p.source⟩, Metric.mem_ball_self hδ⟩ ⟨t, rfl⟩

/-! ### Distances between sets -/

/-- The distance `inf {D x y : x ∈ K, y ∈ L}` between two sets, in `[0, ∞]`. -/
noncomputable def setPairInf (D : ℂ → ℂ → ℝ) (K L : Set ℂ) : ℝ≥0∞ :=
  ⨅ x ∈ K, ⨅ y ∈ L, ENNReal.ofReal (D x y)

theorem setPairInf_singleton (D : ℂ → ℂ → ℝ) (w : ℂ) (L : Set ℂ) :
    setPairInf D {w} L = ⨅ y ∈ L, ENNReal.ofReal (D w y) := by
  simp [setPairInf]

/-- Scaling identity: if `D(r x, r y) = c · E(x, y)` with `0 < c < ∞`, then the distance for `D` between the dilated
sets is `c` times the distance for `E`. -/
theorem setPairInf_smul {D E : ℂ → ℂ → ℝ} {r : ℝ} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcT : c ≠ ⊤)
    (hDE : ∀ x y : ℂ, ENNReal.ofReal (D ((r : ℂ) * x) ((r : ℂ) * y)) = c * ENNReal.ofReal (E x y))
    (K L : Set ℂ) :
    setPairInf D ((fun x : ℂ => (r : ℂ) * x) '' K) ((fun x : ℂ => (r : ℂ) * x) '' L) = c * setPairInf E K L := by
  unfold setPairInf
  simp only [iInf_image, hDE, ENNReal.mul_iInf_of_ne hc0 hcT]

/-- For a jointly continuous `D`, the distance between two sets is the distance between dense subsets. -/
theorem setPairInf_eq_of_dense {D : ℂ → ℂ → ℝ} (hDc : Continuous fun p : ℂ × ℂ => D p.1 p.2)
    {K L A B : Set ℂ} (hAK : A ⊆ K) (hKA : K ⊆ closure A) (hBL : B ⊆ L) (hLB : L ⊆ closure B) :
    setPairInf D K L = setPairInf D A B := by
  apply le_antisymm
  · exact le_iInf₂ fun x hx => le_iInf₂ fun y hy => (iInf₂_le x (hAK hx)).trans (iInf₂_le y (hBL hy))
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    have hU : IsOpen {q : ℂ × ℂ | ENNReal.ofReal (D q.1 q.2) < c} :=
      isOpen_lt (ENNReal.continuous_ofReal.comp hDc) continuous_const
    have hmem : ((x, y) : ℂ × ℂ) ∈ closure (A ×ˢ B) := by
      rw [closure_prod_eq]
      exact ⟨hKA hx, hLB hy⟩
    obtain ⟨q, hqU, hqAB⟩ := mem_closure_iff.1 hmem _ hU hc
    exact ((iInf₂_le q.1 hqAB.1).trans (iInf₂_le q.2 hqAB.2)).trans hqU.le

theorem measurable_setPairInf {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {A B : Set ℂ} (hA : A.Countable) (hB : B.Countable) :
    Measurable[distributionMeasurableSpace] fun T => setPairInf (𝔇 T) A B :=
  Measurable.biInf A hA fun x _ => Measurable.biInf B hB fun y _ =>
    ENNReal.measurable_ofReal.comp (h𝔇.measurable_apply x y)

/-! ### Lower bound for the distance around an annulus -/

/-- The radial segment `{z₀ + s u : a ≤ s ≤ b}`. -/
def radialSegment (z₀ : ℂ) (a b : ℝ) (u : ℂ) : Set ℂ :=
  (fun s : ℝ => z₀ + (s : ℂ) * u) '' Icc a b

theorem radialSegment_smul {r : ℝ} (hr : 0 < r) (z₀ : ℂ) (a b : ℝ) (u : ℂ) :
    (fun x : ℂ => (r : ℂ) * x) '' radialSegment z₀ a b u = radialSegment ((r : ℂ) * z₀) (r * a) (r * b) u := by
  unfold radialSegment
  rw [image_image]
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨r * s, ⟨mul_le_mul_of_nonneg_left hs.1 hr.le, mul_le_mul_of_nonneg_left hs.2 hr.le⟩, ?_⟩
    push_cast
    ring
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s / r, ⟨(le_div_iff₀ hr).2 (by linarith [hs.1]), (div_le_iff₀ hr).2 (by linarith [hs.2])⟩, ?_⟩
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    push_cast
    field_simp

theorem isEuclideanLengthMetric_nonneg {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) :
    0 ≤ D x y := by
  have h := hD.triangle x y x
  rw [hD.self_eq_zero, hD.symm y x] at h
  linarith

/-- Every closed path separating the boundary circles of `A(z₀; a, b)` meets the two radial segments in the directions
`1` and `-1`, so its `D`-length is at least the `D`-distance between these segments. -/
theorem setPairInf_le_pfefferAround {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {z₀ : ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    setPairInf D (radialSegment z₀ a b 1) (radialSegment z₀ a b (-1)) ≤ pfefferAround D z₀ a b := by
  refine le_iInf fun z => le_iInf fun P => le_iInf fun hP => ?_
  have hit : ∀ u : ℂ, ‖u‖ = 1 → ∃ s : I, P s ∈ radialSegment z₀ a b u := by
    intro u hu
    let β : Path (z₀ + (a : ℂ) * u) (z₀ + (b : ℂ) * u) :=
      ⟨⟨fun t => z₀ + ((a + (t : ℝ) * (b - a) : ℝ) : ℂ) * u, by fun_prop⟩, by simp, by simp⟩
    have hsph : ∀ c : ℝ, 0 ≤ c → z₀ + (c : ℂ) * u ∈ Metric.sphere z₀ c := fun c hc => by
      rw [Metric.mem_sphere, Complex.dist_eq, add_sub_cancel_left, norm_mul, hu, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hc]
    obtain ⟨t, s, hs⟩ := hP _ _ β (hsph a ha) (hsph b (ha.trans hab))
    refine ⟨s, a + (t : ℝ) * (b - a), ⟨?_, ?_⟩, hs.symm⟩
    · nlinarith [t.2.1]
    · nlinarith [t.2.2]
  obtain ⟨s, hs⟩ := hit 1 (by simp)
  obtain ⟨s', hs'⟩ := hit (-1) (by simp)
  have hle : ENNReal.ofReal (D (P s) (P s')) ≤ pathLength D P := by
    rcases le_total s s' with h | h
    · rw [hD.symm]
      exact ofReal_le_pathLength_of_le D P h
    · exact ofReal_le_pathLength_of_le D P h
  exact ((iInf₂_le _ hs).trans (iInf₂_le _ hs')).trans hle

/-- For a continuous metric, the two radial segments are at positive distance. -/
theorem exists_pos_le_setPairInf {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (z₀ : ℂ) {a b : ℝ}
    (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal c ≤ setPairInf D (radialSegment z₀ a b 1) (radialSegment z₀ a b (-1)) := by
  obtain ⟨c, hc, hcle⟩ := compact_euclidean_separation (isEuclideanLengthMetric_continuous hD)
    (isEuclideanLengthMetric_nonneg hD) hD.eq_of_eq_zero (isCompact_closedBall z₀ b) (by linarith : 0 < 2 * a)
  refine ⟨c, hc, le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal ?_⟩
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨s', hs', rfl⟩ := hy
  have hball : ∀ (t : ℝ) (u : ℂ), ‖u‖ = 1 → t ∈ Icc a b → z₀ + (t : ℂ) * u ∈ Metric.closedBall z₀ b :=
    fun t u hu ht => by
      rw [Metric.mem_closedBall, Complex.dist_eq, add_sub_cancel_left, norm_mul, hu, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (ha.le.trans ht.1)]
      exact ht.2
  refine hcle _ (hball s 1 (by simp) hs) _ (hball s' (-1) (by simp) hs') ?_
  rw [Complex.dist_eq, show z₀ + (s : ℂ) * 1 - (z₀ + (s' : ℂ) * -1) = ((s + s' : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_of_nonneg (by linarith [hs.1, hs'.1])]
  linarith [hs.1, hs'.1]

/-! ### Upper bound for the distance around an annulus -/

/-- The sum `∑_{j < k} D(w_j, w_{j+1})` along the points `w_j = circlePoint z₀ ρ k j`. -/
noncomputable def chainSum (D : ℂ → ℂ → ℝ) (z₀ : ℂ) (ρ : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range k, ENNReal.ofReal (D (circlePoint z₀ ρ k j) (circlePoint z₀ ρ k (j + 1)))

/-- Each step `D(w_j, w_{j+1})` is smaller than the `D`-distance from `w_j` to the circle `∂B_δ(w_j)`. -/
def ChainGood (D : ℂ → ℂ → ℝ) (z₀ : ℂ) (ρ δ : ℝ) (k : ℕ) : Prop :=
  ∀ j < k, ENNReal.ofReal (D (circlePoint z₀ ρ k j) (circlePoint z₀ ρ k (j + 1))) <
    setPairInf D {circlePoint z₀ ρ k j} (Metric.sphere (circlePoint z₀ ρ k j) δ)

/-- If the chain of `k ≥ 2` points on `∂B_ρ(z₀)` is good, then near-geodesics between consecutive points form a closed
path in `{ρ - δ < |w - z₀| < ρ + δ}` around `z₀`; it separates the boundary circles of `A(z₀; a, b)`. -/
theorem pfefferAround_le_chainSum {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {z₀ : ℂ} {a b ρ δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (h₁ : a + δ ≤ ρ) (h₂ : ρ + δ ≤ b) {k : ℕ} (hk : 2 ≤ k)
    (hgood : ChainGood D z₀ ρ δ k) : pfefferAround D z₀ a b ≤ chainSum D z₀ ρ k := by
  have hnonneg := isEuclideanLengthMetric_nonneg hD
  have hρ : 0 < ρ := by linarith
  have hk0 : k ≠ 0 := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεk : (0 : ℝ) < ε / k := div_pos (by exact_mod_cast hε) hkpos
  have hpath : ∀ j, ∃ p : Path (circlePoint z₀ ρ k j) (circlePoint z₀ ρ k (j + 1)),
      (j < k → ∀ t, p t ∈ Metric.ball (circlePoint z₀ ρ k j) δ) ∧
      pathLength D p ≤ ENNReal.ofReal (D (circlePoint z₀ ρ k j) (circlePoint z₀ ρ k (j + 1))) +
        ENNReal.ofReal (ε / k) := by
    intro j
    by_cases hj : j < k
    · have hlt := hgood j hj
      rw [setPairInf_singleton] at hlt
      set d := D (circlePoint z₀ ρ k j) (circlePoint z₀ ρ k (j + 1)) with hd
      obtain ⟨r, -, hdr, hrm⟩ := ENNReal.lt_iff_exists_real_btwn.1 hlt
      have hdr' : d < r := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hnonneg _ _)).1 hdr
      have hη : 0 < min (r - d) (ε / k) := lt_min (by linarith) hεk
      obtain ⟨p, hp⟩ := hD.exists_pathLength_lt hnonneg _ _ hη
      have hmin := min_le_left (r - d) (ε / k)
      have hpr : pathLength D p < ENNReal.ofReal r :=
        hp.trans_le (ENNReal.ofReal_le_ofReal (by rw [add_comm]; exact le_sub_iff_add_le.1 hmin))
      refine ⟨p, fun _ => mem_ball_of_pathLength_lt hD p hδ (fun y hy => hpr.trans_le ?_), ?_⟩
      · exact hrm.le.trans (iInf₂_le y hy)
      · refine hp.le.trans ?_
        rw [ENNReal.ofReal_add (hnonneg _ _) hη.le]
        gcongr
        exact min_le_right _ _
    · obtain ⟨p, hp⟩ := hD.exists_pathLength_lt hnonneg (circlePoint z₀ ρ k j) (circlePoint z₀ ρ k (j + 1)) hεk
      refine ⟨p, fun h => absurd h hj, hp.le.trans ?_⟩
      rw [ENNReal.ofReal_add (hnonneg _ _) hεk.le]
  choose p hpball hplen using hpath
  let R : Set ℂ := {v | ρ - δ < ‖v - z₀‖ ∧ ‖v - z₀‖ < ρ + δ}
  have hring : ∀ j < k, ∀ t, p j t ∈ R := by
    intro j hj t
    have hb := hpball j hj t
    rw [Metric.mem_ball, Complex.dist_eq] at hb
    have hn := norm_circlePoint_sub z₀ hρ.le k j
    have e1 := norm_add_le (p j t - circlePoint z₀ ρ k j) (circlePoint z₀ ρ k j - z₀)
    have e2 := norm_add_le (circlePoint z₀ ρ k j - p j t) (p j t - z₀)
    rw [sub_add_sub_cancel] at e1 e2
    rw [norm_sub_rev (circlePoint z₀ ρ k j) (p j t)] at e2
    show ρ - δ < ‖p j t - z₀‖ ∧ ‖p j t - z₀‖ < ρ + δ
    exact ⟨by linarith, by linarith⟩
  have hw0 : circlePoint z₀ ρ k 0 ∈ R := by
    show ρ - δ < ‖circlePoint z₀ ρ k 0 - z₀‖ ∧ ‖circlePoint z₀ ρ k 0 - z₀‖ < ρ + δ
    rw [norm_circlePoint_sub z₀ hρ.le]
    exact ⟨by linarith, by linarith⟩
  have hkk : circlePoint z₀ ρ k 0 = circlePoint z₀ ρ k k := (circlePoint_self z₀ ρ hk0).symm
  have hR0 : ∀ v ∈ R, v ≠ z₀ := fun v hv h0 => by
    have := hv.1
    rw [h0, sub_self, norm_zero] at this
    linarith
  have hch : ∀ t, chainPath (circlePoint z₀ ρ k) p k t ∈ R := chainPath_mem hw0 k hring
  have hstep : ∀ j < k, windIncr (p j) z₀ = ((2 * Real.pi / k : ℝ) : ℂ) * Complex.I := by
    intro j hj
    have hn := norm_circlePoint_sub z₀ hρ.le k j
    have hu : circlePoint z₀ ρ k j - z₀ ≠ 0 := norm_ne_zero_iff.1 (by rw [hn]; exact hρ.ne')
    have hre : ∀ t, 0 < ((p j t - z₀) / (circlePoint z₀ ρ k j - z₀)).re := fun t => by
      refine re_div_pos_of_norm_lt ?_
      have hb := hpball j hj t
      rw [Metric.mem_ball, Complex.dist_eq] at hb
      rw [hn]
      linarith
    have him : (((2 * Real.pi / k : ℝ) : ℂ) * Complex.I).im = 2 * Real.pi / k := by simp
    rw [windIncr_of_re_pos (p j) hu hre, div_self hu, Complex.log_one, sub_zero,
      circlePoint_ratio z₀ hρ.ne' k j, Complex.log_exp]
    · rw [him]
      exact (neg_neg_of_pos Real.pi_pos).trans (div_pos (mul_pos two_pos Real.pi_pos) hkpos)
    · rw [him, div_le_iff₀ hkpos]
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith [Real.pi_pos]
  have hwind : windIncr ((chainPath (circlePoint z₀ ρ k) p k).cast rfl hkk) z₀ ≠ 0 := by
    rw [windIncr_cast _ rfl hkk z₀ (fun t => hR0 _ (hch t)),
      windIncr_chainPath (hR0 _ hw0) k (fun j hj t => hR0 _ (hring j hj t)),
      Finset.sum_congr rfl (fun j hj => hstep j (Finset.mem_range.1 hj)), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have : (k : ℂ) * (((2 * Real.pi / k : ℝ) : ℂ) * Complex.I) = 2 * Real.pi * Complex.I := by
      have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0
      push_cast
      field_simp
    rw [this]
    exact Complex.two_pi_I_ne_zero
  have hsep : PfefferSeparates ((chainPath (circlePoint z₀ ρ k) p k).cast rfl hkk) z₀ a b :=
    separates_of_windIncr_ne_zero _ (fun s => lt_of_le_of_lt (by linarith) (hch s).1)
      (fun s => lt_of_lt_of_le (hch s).2 (by linarith)) hwind
  have hsum : ∑ j ∈ Finset.range k, (ENNReal.ofReal (D (circlePoint z₀ ρ k j) (circlePoint z₀ ρ k (j + 1))) +
      ENNReal.ofReal (ε / k)) = chainSum D z₀ ρ k + ε := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, chainSum,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg k),
      show (k : ℝ) * (ε / k) = ε by field_simp, ENNReal.ofReal_coe_nnreal]
  calc pfefferAround D z₀ a b
      ≤ pathLength D ((chainPath (circlePoint z₀ ρ k) p k).cast rfl hkk) :=
        iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le hsep le_rfl))
    _ = pathLength D (chainPath (circlePoint z₀ ρ k) p k) := rfl
    _ ≤ ∑ j ∈ Finset.range k, pathLength D (p j) := pathLength_chainPath_le hD p k
    _ ≤ ∑ j ∈ Finset.range k, (ENNReal.ofReal (D (circlePoint z₀ ρ k j) (circlePoint z₀ ρ k (j + 1))) +
          ENNReal.ofReal (ε / k)) := Finset.sum_le_sum fun j _ => hplen j
    _ = chainSum D z₀ ρ k + ε := hsum

/-- For a continuous metric, every chain with sufficiently many points is good. -/
theorem exists_chainGood {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (z₀ : ℂ) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ : 0 < δ) : ∃ K : ℕ, ∀ k ≥ K, ChainGood D z₀ ρ δ k := by
  have hDc := isEuclideanLengthMetric_continuous hD
  set B := Metric.closedBall z₀ (ρ + δ)
  have hB : IsCompact B := isCompact_closedBall z₀ (ρ + δ)
  obtain ⟨m, hm, hmle⟩ := compact_euclidean_separation hDc (isEuclideanLengthMetric_nonneg hD) hD.eq_of_eq_zero
    hB hδ
  have huc := (hB.prod hB).uniformContinuousOn_of_continuous hDc.continuousOn
  obtain ⟨η, hη, hηD⟩ := Metric.uniformContinuousOn_iff.1 huc m hm
  have hcont : Continuous fun θ : ℝ => ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ := by fun_prop
  have ht : Tendsto (fun k : ℕ => ‖Complex.exp (((2 * Real.pi / k : ℝ) : ℂ) * Complex.I) - 1‖) atTop (𝓝 0) := by
    have := (hcont.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi))
    simpa [Function.comp_def] using this
  have hpos : (0 : ℝ) < η / ρ := div_pos hη hρ
  obtain ⟨K, hK⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hpos))
  refine ⟨K, fun k hk j _ => ?_⟩
  have hn := norm_circlePoint_sub z₀ hρ.le k j
  have hwB : circlePoint z₀ ρ k j ∈ B := by
    rw [Metric.mem_closedBall, Complex.dist_eq, hn]
    linarith
  have hstep : ‖circlePoint z₀ ρ k (j + 1) - circlePoint z₀ ρ k j‖ < η := by
    have hu : circlePoint z₀ ρ k j - z₀ ≠ 0 := norm_ne_zero_iff.1 (by rw [hn]; exact hρ.ne')
    have heq : circlePoint z₀ ρ k (j + 1) - circlePoint z₀ ρ k j =
        (circlePoint z₀ ρ k j - z₀) * (Complex.exp (((2 * Real.pi / k : ℝ) : ℂ) * Complex.I) - 1) := by
      rw [← circlePoint_ratio z₀ hρ.ne' k j]
      field_simp
      ring
    rw [heq, norm_mul, hn]
    have := hK k hk
    rw [lt_div_iff₀ hρ] at this
    linarith
  have hw1B : circlePoint z₀ ρ k (j + 1) ∈ B := by
    rw [Metric.mem_closedBall, Complex.dist_eq, norm_circlePoint_sub z₀ hρ.le]
    linarith
  have hsmall : D (circlePoint z₀ ρ k j) (circlePoint z₀ ρ k (j + 1)) < m := by
    have h1 := hηD (circlePoint z₀ ρ k j, circlePoint z₀ ρ k (j + 1)) ⟨hwB, hw1B⟩
      (circlePoint z₀ ρ k j, circlePoint z₀ ρ k j) ⟨hwB, hwB⟩ (by
        rw [Prod.dist_eq, dist_self, Complex.dist_eq]
        exact max_lt hη hstep)
    rw [hD.self_eq_zero, Real.dist_eq, sub_zero] at h1
    exact (le_abs_self _).trans_lt h1
  calc ENNReal.ofReal (D (circlePoint z₀ ρ k j) (circlePoint z₀ ρ k (j + 1)))
      < ENNReal.ofReal m := (ENNReal.ofReal_lt_ofReal_iff hm).2 hsmall
    _ ≤ setPairInf D {circlePoint z₀ ρ k j} (Metric.sphere (circlePoint z₀ ρ k j) δ) := by
      rw [setPairInf_singleton]
      refine le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal (hmle _ hwB _ ?_ ?_)
      · have hy' := Metric.mem_sphere.1 hy
        rw [Metric.mem_closedBall]
        have := dist_triangle y (circlePoint z₀ ρ k j) z₀
        rw [Complex.dist_eq (circlePoint z₀ ρ k j), hn] at this
        linarith
      · rw [dist_comm]
        exact (Metric.mem_sphere.1 hy).ge

/-! ### The normalization of the pure field -/

theorem pfefferCircleAverage_zero (r : ℝ) (z : ℂ) : pfefferCircleAverage (fun _ => 0) r z = 0 := by
  simp [pfefferCircleAverage]

theorem pfefferField_zero {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) :
    pfefferField hC (fun _ _ => 0) ω = hC ω :=
  addFunPairing_const_zero (hC ω)

/-- With `f = 0` and `c_r = r^{ξQ}`, the normalization of Axiom V is `r^{-ξQ} e^{-ξ h_r(0)}`. -/
theorem pfefferNormalization_zero {Ω : Type*} (γ ξ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) {r : ℝ} (hr : 0 < r) (ω : Ω) :
    pfefferNormalization ξ hcirc (fun _ _ => 0) (fun r => r ^ (ξ * lqgQ γ)) r ω =
      zeroChargeNormalization γ ξ hcirc r ω := by
  simp only [pfefferNormalization, zeroChargeNormalization, pfefferCircleAverage_zero, add_zero,
    Real.rpow_neg hr.le]

end PureGFFCrossing

open PureGFFCrossing

/-! ### Axiom V(b) for the pure field -/

/-- **Tightness across the annulus.** For a `γ`-LQG metric `𝔇` and a whole-plane GFF `h`, with `c_r = r^{ξQ}`, the
normalized distances `c_r⁻¹ e^{-ξ h_r(0)} D_h(across A(r z₀; r a, r b))` are tight and reciprocally tight over `r > 0`. -/
theorem pureGFF_pfefferAcross_tight {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {z₀ : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    PfefferTightAcrossScales P (fun r ω => pfefferNormalization ξ hcirc (fun _ _ => 0)
      (fun r => r ^ (ξ * lqgQ γ)) r ω *
        pfefferAcross (𝔇 (pfefferField hC (fun _ _ => 0) ω)) ((r : ℂ) * z₀) (r * a) (r * b)) := by
  intro ε hε0 hε1
  obtain ⟨M, hM, hMr⟩ := normalizedAcross_tight h𝔇 h ha hab ε hε0 hε1
  refine ⟨M, hM, fun r hr => ?_⟩
  have heq : ∀ ω, pfefferNormalization ξ hcirc (fun _ _ => 0) (fun r => r ^ (ξ * lqgQ γ)) r ω *
      pfefferAcross (𝔇 (pfefferField hC (fun _ _ => 0) ω)) ((r : ℂ) * z₀) (r * a) (r * b) =
        normalizedAcross γ ξ hC hcirc 𝔇 z₀ a b r ω := fun ω => by
    rw [pfefferNormalization_zero γ ξ hcirc hr ω, pfefferField_zero]
    rfl
  simp only [heq]
  exact hMr r hr

/-- **Tightness around the annulus.** For a `γ`-LQG metric `𝔇` and a whole-plane GFF `h`, with `c_r = r^{ξQ}`, the
normalized distances `c_r⁻¹ e^{-ξ h_r(0)} D_h(around A(r z₀; r a, r b))` are tight and reciprocally tight over `r > 0`. -/
theorem pureGFF_pfefferAround_tight {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {z₀ : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    PfefferTightAcrossScales P (fun r ω => pfefferNormalization ξ hcirc (fun _ _ => 0)
      (fun r => r ^ (ξ * lqgQ γ)) r ω *
        pfefferAround (𝔇 (pfefferField hC (fun _ _ => 0) ω)) ((r : ℂ) * z₀) (r * a) (r * b)) := by
  intro ε hε0 hε1
  have : IsProbabilityMeasure P := h.isProbabilityMeasure
  set ρ : ℝ := (a + b) / 2 with hρ
  set δ : ℝ := (b - a) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have h₁ : a + δ ≤ ρ := by rw [hρ, hδ]; linarith
  have h₂ : ρ + δ ≤ b := by rw [hρ, hδ]; linarith
  obtain ⟨Ap, hApc, hApS, hApd⟩ := TopologicalSpace.exists_countable_dense_subset (radialSegment z₀ a b 1)
  obtain ⟨Am, hAmc, hAmS, hAmd⟩ := TopologicalSpace.exists_countable_dense_subset (radialSegment z₀ a b (-1))
  choose B hBc hBS hBd using fun k j : ℕ => exists_countable_dense_sphere (circlePoint z₀ ρ k j) δ
  let good : ℕ → ℕ → Set ((ℂ → ℝ) → ℝ) := fun n k =>
    (⋂ j ∈ Iio k, {T | ENNReal.ofReal (𝔇 T (circlePoint z₀ ρ k j) (circlePoint z₀ ρ k (j + 1))) <
        setPairInf (𝔇 T) {circlePoint z₀ ρ k j} (B k j)}) ∩
      {T | chainSum (𝔇 T) z₀ ρ k ≤ ENNReal.ofReal ((n : ℝ) + 1)}
  let S : ℕ → Set ((ℂ → ℝ) → ℝ) := fun n =>
    {T | ENNReal.ofReal ((n : ℝ) + 1)⁻¹ ≤ setPairInf (𝔇 T) Ap Am} ∩ ⋃ k ∈ Icc 2 n, good n k
  have hSm : ∀ n, MeasurableSet[distributionMeasurableSpace] (S n) := fun n =>
    (measurableSet_le measurable_const (measurable_setPairInf h𝔇 hApc hAmc)).inter
      (MeasurableSet.biUnion (to_countable _) fun k _ =>
        (MeasurableSet.biInter (to_countable _) fun j _ =>
          measurableSet_lt (ENNReal.measurable_ofReal.comp (h𝔇.measurable_apply _ _))
            (measurable_setPairInf h𝔇 (countable_singleton _) (hBc k j))).inter
        (measurableSet_le (Finset.measurable_sum _ fun j _ =>
          ENNReal.measurable_ofReal.comp (h𝔇.measurable_apply _ _)) measurable_const))
  have hSmono : Monotone S := by
    intro m n hmn T hT
    obtain ⟨hL, hU⟩ := hT
    obtain ⟨k, hk, hj, hs⟩ := mem_iUnion₂.1 hU
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    refine ⟨le_trans (ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity) hmn')) hL,
      mem_iUnion₂.2 ⟨k, ⟨hk.1, hk.2.trans hmn⟩, hj, hs.trans (ENNReal.ofReal_le_ofReal hmn')⟩⟩
  have hCax := zeroCharge_satisfies h𝔇 h
  have hcover : ∀ᵐ ω ∂P, ω ∈ ⋃ n, hC ⁻¹' S n := by
    filter_upwards [hCax.ae_isEuclideanLengthMetric] with ω hD
    have hDc := isEuclideanLengthMetric_continuous hD
    obtain ⟨c, hc, hcL⟩ := exists_pos_le_setPairInf hD z₀ (b := b) ha
    obtain ⟨K, hK⟩ := exists_chainGood hD z₀ hρ0 hδ0
    have hgood := hK (max K 2) (le_max_left _ _)
    have hsum : chainSum (𝔇 (hC ω)) z₀ ρ (max K 2) ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun j _ => ENNReal.ofReal_ne_top
    obtain ⟨n₁, hn₁⟩ := exists_nat_ge (1 / c)
    obtain ⟨n₃, hn₃⟩ := exists_nat_ge (chainSum (𝔇 (hC ω)) z₀ ρ (max K 2)).toReal
    set N := max (max n₁ (max K 2)) n₃ with hN
    have hN1 : (n₁ : ℝ) ≤ N := by exact_mod_cast (le_max_left _ _).trans (le_max_left _ _)
    have hN3 : (n₃ : ℝ) ≤ N := by exact_mod_cast le_max_right _ _
    refine mem_iUnion.2 ⟨N, ?_, ?_⟩
    · show ENNReal.ofReal ((N : ℝ) + 1)⁻¹ ≤ setPairInf (𝔇 (hC ω)) Ap Am
      rw [← setPairInf_eq_of_dense hDc hApS hApd hAmS hAmd]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hcL
      have : c⁻¹ ≤ (N : ℝ) + 1 := by
        rw [← one_div]
        linarith
      exact (inv_le_comm₀ (by positivity) hc).2 this
    · refine mem_iUnion₂.2 ⟨max K 2, ⟨le_max_right _ _, (le_max_right _ _).trans (le_max_left _ _)⟩, ?_, ?_⟩
      · refine mem_iInter₂.2 fun j hj => ?_
        show ENNReal.ofReal (𝔇 (hC ω) (circlePoint z₀ ρ (max K 2) j) (circlePoint z₀ ρ (max K 2) (j + 1))) <
          setPairInf (𝔇 (hC ω)) {circlePoint z₀ ρ (max K 2) j} (B (max K 2) j)
        rw [← setPairInf_eq_of_dense hDc subset_rfl subset_closure (hBS _ j) (hBd _ j)]
        exact hgood j hj
      · show chainSum (𝔇 (hC ω)) z₀ ρ (max K 2) ≤ ENNReal.ofReal ((N : ℝ) + 1)
        rw [← ENNReal.ofReal_toReal hsum]
        exact ENNReal.ofReal_le_ofReal (by linarith)
  have hunion : P (⋃ n, hC ⁻¹' S n) = 1 := by
    rw [measure_congr ((ae_eq_univ (s := ⋃ n, hC ⁻¹' S n)).2 (ae_iff.1 hcover)), measure_univ]
  have hlim : Tendsto (fun n => P (hC ⁻¹' S n)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := P) (fun m n hmn => preimage_mono (f := hC) (hSmono hmn))
    rwa [hunion] at this
  have hlt : ENNReal.ofReal (1 - ε) < 1 := ENNReal.ofReal_lt_one.2 (by linarith)
  obtain ⟨N, hN⟩ := (hlim.eventually (lt_mem_nhds hlt)).exists
  refine ⟨(N : ℝ) + 1, by positivity, fun r hr => ?_⟩
  have hg : IsWholePlaneGFF P (affinePairing hC hcirc (r : ℂ) 0) (affineCircle hcirc (r : ℂ) 0) :=
    wholePlaneGFFAffineInvariance_proved P hC hcirc h (r : ℂ) (by exact_mod_cast hr.ne') 0
  have hgax := zeroCharge_satisfies h𝔇 hg
  let Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞ := (S N).indicator fun _ => 1
  have hΦ : Measurable[distributionMeasurableSpace] Φ := measurable_const.indicator (hSm N)
  obtain ⟨F, hFm, hFeq⟩ := exists_common_observable_of_distribution_measurable Φ hΦ
  have hdF : IdentDistrib (fun ω => Φ (affinePairing hC hcirc (r : ℂ) 0 ω)) (fun ω => Φ (hC ω)) P P := by
    have := (hg.identDistrib_observables_across_spaces h).comp hFm
    simp only [Function.comp_def, hFeq] at this
    exact this
  have hpre : ∀ f : Ω → (ℂ → ℝ) → ℝ, (fun ω => Φ (f ω)) ⁻¹' {1} = f ⁻¹' S N := fun f => by
    ext ω
    simp [Φ]
  have hlaw : P (affinePairing hC hcirc (r : ℂ) 0 ⁻¹' S N) = P (hC ⁻¹' S N) := by
    rw [← hpre, ← hpre]
    exact hdF.measure_mem_eq (measurableSet_singleton 1)
  calc ENNReal.ofReal (1 - ε) ≤ P (hC ⁻¹' S N) := hN.le
    _ = P (affinePairing hC hcirc (r : ℂ) 0 ⁻¹' S N) := hlaw.symm
    _ ≤ _ := measure_mono_ae ?_
  filter_upwards [zeroCharge_scale_ae h𝔇 h hr, hgax.ae_isEuclideanLengthMetric,
    hCax.ae_isEuclideanLengthMetric] with ω hsc hDt hD hmem
  obtain ⟨hL, hU⟩ := hmem
  obtain ⟨k, hk, hj, hs⟩ := mem_iUnion₂.1 hU
  have hDtc := isEuclideanLengthMetric_continuous hDt
  set κ := ENNReal.ofReal (Real.exp (ξ * (hcirc ω r 0 + lqgQ γ * Real.log r))) with hκ
  have hκ0 : κ ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hκT : κ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hNκ : zeroChargeNormalization γ ξ hcirc r ω * κ = 1 := zeroChargeNormalization_mul hr (hcirc ω r 0)
  have hlow : κ * ENNReal.ofReal ((N : ℝ) + 1)⁻¹ ≤ pfefferAround (𝔇 (hC ω)) ((r : ℂ) * z₀) (r * a) (r * b) := by
    calc κ * ENNReal.ofReal ((N : ℝ) + 1)⁻¹
        ≤ κ * setPairInf (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) Ap Am := by gcongr; exact hL
      _ = κ * setPairInf (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) (radialSegment z₀ a b 1)
            (radialSegment z₀ a b (-1)) := by
          rw [setPairInf_eq_of_dense hDtc hApS hApd hAmS hAmd]
      _ = setPairInf (𝔇 (hC ω)) ((fun x : ℂ => (r : ℂ) * x) '' radialSegment z₀ a b 1)
            ((fun x : ℂ => (r : ℂ) * x) '' radialSegment z₀ a b (-1)) := (setPairInf_smul hκ0 hκT hsc _ _).symm
      _ = setPairInf (𝔇 (hC ω)) (radialSegment ((r : ℂ) * z₀) (r * a) (r * b) 1)
            (radialSegment ((r : ℂ) * z₀) (r * a) (r * b) (-1)) := by
          rw [radialSegment_smul hr, radialSegment_smul hr]
      _ ≤ _ := setPairInf_le_pfefferAround hD (by positivity) (mul_le_mul_of_nonneg_left hab.le hr.le)
  have hgoodt : ChainGood (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) z₀ ρ δ k := fun j hjk => by
    rw [setPairInf_eq_of_dense hDtc subset_rfl subset_closure (hBS k j) (hBd k j)]
    exact mem_iInter₂.1 hj j (mem_Iio.2 hjk)
  have hgoodD : ChainGood (𝔇 (hC ω)) ((r : ℂ) * z₀) (r * ρ) (r * δ) k := fun j hjk => by
    have hsing : ({(r : ℂ) * circlePoint z₀ ρ k j} : Set ℂ) =
        (fun x : ℂ => (r : ℂ) * x) '' {circlePoint z₀ ρ k j} := image_singleton.symm
    rw [circlePoint_smul, circlePoint_smul, hsc, sphere_smul_eq_image hr, hsing, setPairInf_smul hκ0 hκT hsc]
    exact ENNReal.mul_lt_mul_right hκ0 hκT (hgoodt j hjk)
  have hup : pfefferAround (𝔇 (hC ω)) ((r : ℂ) * z₀) (r * a) (r * b) ≤
      κ * chainSum (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) z₀ ρ k := by
    calc pfefferAround (𝔇 (hC ω)) ((r : ℂ) * z₀) (r * a) (r * b)
        ≤ chainSum (𝔇 (hC ω)) ((r : ℂ) * z₀) (r * ρ) k :=
          pfefferAround_le_chainSum hD (by positivity) (by positivity)
            (by rw [← mul_add]; exact mul_le_mul_of_nonneg_left h₁ hr.le)
            (by rw [← mul_add]; exact mul_le_mul_of_nonneg_left h₂ hr.le) hk.1 hgoodD
      _ = κ * chainSum (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) z₀ ρ k := by
          unfold chainSum
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [circlePoint_smul, circlePoint_smul, hsc]
  rw [pfefferNormalization_zero γ ξ hcirc hr ω, pfefferField_zero]
  constructor
  · calc ENNReal.ofReal ((N : ℝ) + 1)⁻¹
        = zeroChargeNormalization γ ξ hcirc r ω * (κ * ENNReal.ofReal ((N : ℝ) + 1)⁻¹) := by
          rw [← mul_assoc, hNκ, one_mul]
      _ ≤ _ := by gcongr
  · calc zeroChargeNormalization γ ξ hcirc r ω * pfefferAround (𝔇 (hC ω)) ((r : ℂ) * z₀) (r * a) (r * b)
        ≤ zeroChargeNormalization γ ξ hcirc r ω *
            (κ * chainSum (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) z₀ ρ k) := by gcongr
      _ = chainSum (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) z₀ ρ k := by rw [← mul_assoc, hNκ, one_mul]
      _ ≤ _ := hs

/-- **Axiom V of Pfeffer's Definition 1.6 for the pure whole-plane GFF.** For a `γ`-LQG metric `𝔇` with Weyl
exponent `ξ` and a whole-plane GFF `h` (the field `h^ℂ + f` with `f = 0`), the scaling constants `c_r = r^{ξQ}`,
`Q = 2/γ + γ/2`, satisfy (a) positivity, (b) tightness and reciprocal tightness across and around every scaled annulus,
and (c) the bound (1.7). -/
theorem IsLQGMetric.pureGFF_pfefferAxiomVScale {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) :
    PfefferAxiomVScale P ξ 𝔇 hC hcirc (fun _ _ => 0) (fun r => r ^ (ξ * lqgQ γ)) := by
  refine ⟨fun r hr => Real.rpow_pos_of_pos hr _, fun z₀ a b ha hab =>
    ⟨pureGFF_pfefferAcross_tight h𝔇 h ha hab, pureGFF_pfefferAround_tight h𝔇 h ha hab⟩, ?_⟩
  set s := ξ * lqgQ γ
  have hΛ1 : 1 ≤ |s| + 2 := by linarith [abs_nonneg s]
  refine ⟨|s| + 2, by linarith [abs_nonneg s], fun δ hδ0 hδ1 q hq => ?_⟩
  have hratio : (δ * q) ^ s / (q : ℝ) ^ s = δ ^ s := by
    rw [Real.mul_rpow hδ0.le hq.le, mul_div_assoc, div_self (Real.rpow_pos_of_pos hq s).ne', mul_one]
  dsimp only
  rw [hratio]
  constructor
  · have h1 : δ ^ (|s| + 2) ≤ δ ^ s :=
      Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (by linarith [le_abs_self s])
    have h2 : (|s| + 2)⁻¹ * δ ^ (|s| + 2) ≤ δ ^ (|s| + 2) :=
      mul_le_of_le_one_left (Real.rpow_pos_of_pos hδ0 _).le (inv_le_one_of_one_le₀ hΛ1)
    linarith
  · have h1 : δ ^ s ≤ δ ^ (-(|s| + 2)) :=
      Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (by linarith [neg_abs_le s])
    have h2 : δ ^ (-(|s| + 2)) ≤ (|s| + 2) * δ ^ (-(|s| + 2)) :=
      le_mul_of_one_le_left (Real.rpow_pos_of_pos hδ0 _).le hΛ1
    linarith


end HarmonicBalls
