import HarmonicBalls.FirstPass.S11m.WeylShiftE1
import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.Steps.Sec11.WeylAnnulusBounds

/-!
# Deterministic bounds for the first event `E₁` (fp-S11m, owner z4)

Route: `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md` section 6.2; paper `lem:E1`
(`paper/lqg_harmonic_ball-corrected.tex`, lines 3661-3700). For a Euclidean length metric `D`, a weight `f` with
`weylScaling D ξ f` finite, and `E := (weylScaling D ξ f).toReal`:
* `weylScaling_ge_of_exit`: first exit from `Q` (weight `≥ c` on `closure Q`), target outside `interior Q`.
* `setDist_weylScaling_ge_frontier`: `e^{ξ c} L ≤ L_new` for `L = D(Q̄', ∂Q)` (paper: `L_new = b_Q L`, lower half).
* `setDist_weylScaling_ge_sphere`: `e^{ξ c} D(0, ∂B_{δ/2}) ≤ a₀,new = D_new(0, ∂B_δ)` (paper: `a₀,new ≥ b D(0, ∂B_{δ/2})`).
* `pinchLocalA_weylScaling_le`: `A_new ≤ b A` when the weight is `≤ log b` on `Ω_geom` (paper: "the root bump
  multiplies all lengths in Ω by at most b"); reduces to `IsEuclideanLengthMetric.internalMetric_weylScaling_le`.
No probability and no measurability here. That `E` is a Euclidean length metric is a hypothesis.
-/
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace HarmonicBalls.S11m.E1Bounds

/-- Nonnegativity of a Euclidean length metric. -/
theorem nonneg_of_isEuclideanLengthMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) :
    0 ≤ D x y := by
  have h := hD.triangle x y x
  rw [hD.self_eq_zero, hD.symm y x] at h
  linarith

/-- First-exit lower bound for the Weyl scaling. If `f ≥ c` on `closure Q`, `u ∈ closure Q`, `v ∉ interior Q`,
and `r ≤ D u w` for every `w ∈ ∂Q`, then `e^{ξ c} r ≤ weylScaling D ξ f u v`. Every admissible path from `u` to `v`
leaves `interior Q` through a point `p t₀ ∈ ∂Q`, and before that it stays in `closure Q` where the weight is `≥ c`. -/
theorem weylScaling_ge_of_exit {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ c : ℝ} (hξ : 0 ≤ ξ)
    {f : ℂ → ℝ} {Q : Set ℂ} (hfc : ∀ z ∈ closure Q, c ≤ f z) {u v : ℂ} (hu : u ∈ closure Q)
    (hv : v ∉ interior Q) {r : ℝ} (hr : ∀ w ∈ frontier Q, r ≤ D u w) :
    ENNReal.ofReal (Real.exp (ξ * c) * r) ≤ weylScaling D ξ f u v := by
  unfold weylScaling
  refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 => le_iInf fun hT => ?_
  obtain ⟨hT0, hcont, -⟩ := id hp
  -- first exit time from the interior of `Q`
  set S : Set ℝ := Icc 0 T ∩ p ⁻¹' (interior Q)ᶜ with hS
  have hSc : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isOpen_interior.isClosed_compl
  have hTS : T ∈ S := ⟨⟨hT0, le_rfl⟩, by show p T ∈ (interior Q)ᶜ; rw [hT]; exact hv⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set t₀ := sInf S with ht₀
  have ht₀S : t₀ ∈ S := hSc.csInf_mem ⟨T, hTS⟩ hbdd
  have ht₀le : ∀ t ∈ S, t₀ ≤ t := fun t ht => csInf_le hbdd ht
  have ht₀I : t₀ ∈ Icc 0 T := ht₀S.1
  have hpt₀ : p t₀ ∉ interior Q := ht₀S.2
  have hinside : ∀ t ∈ Ico 0 t₀, p t ∈ interior Q := by
    intro t ht
    by_contra h
    have htS : t ∈ S := ⟨⟨ht.1, le_trans ht.2.le ht₀I.2⟩, h⟩
    exact absurd (ht₀le t htS) (not_le.mpr ht.2)
  have hsub : Ico 0 t₀ ⊆ Icc 0 T ∩ p ⁻¹' closure Q := fun t ht =>
    ⟨⟨ht.1, le_trans ht.2.le ht₀I.2⟩, subset_closure (interior_subset (hinside t ht))⟩
  have hclS : IsClosed (Icc 0 T ∩ p ⁻¹' closure Q) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closure
  -- the path stays in `closure Q` up to `t₀`
  have hcl : ∀ t ∈ Icc 0 t₀, p t ∈ closure Q := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]
      rcases eq_or_lt_of_le ht₀I.1 with h0' | hpos
      · rw [← h0', h0]; exact hu
      · have hmem : t₀ ∈ closure (Ico 0 t₀) := by
          rw [closure_Ico hpos.ne]; exact right_mem_Icc.2 hpos.le
        exact (closure_minimal hsub hclS hmem).2
    · exact subset_closure (interior_subset (hinside t ⟨ht.1, h⟩))
  have hpf : p t₀ ∈ frontier Q := ⟨hcl t₀ ⟨ht₀I.1, le_rfl⟩, hpt₀⟩
  -- the integral over [0, T] dominates the integral over [0, t₀]
  have hint : ∫⁻ _ in Icc 0 t₀, ENNReal.ofReal (Real.exp (ξ * c)) ≤
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
    calc ∫⁻ _ in Icc 0 t₀, ENNReal.ofReal (Real.exp (ξ * c))
        ≤ ∫⁻ t in Icc 0 t₀, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
          apply setLIntegral_mono' measurableSet_Icc
          intro t ht
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.2
          exact mul_le_mul_of_nonneg_left (hfc _ (hcl t ht)) hξ
      _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
          lintegral_mono_set (Icc_subset_Icc le_rfl ht₀I.2)
  have hD0 : D u (p t₀) ≤ t₀ := by
    have := hD.dist_le_of_lengthParametrized hp (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT0⟩) ht₀I
    rwa [h0, sub_zero, abs_of_nonneg ht₀I.1] at this
  have hvol : ∫⁻ _ in Icc 0 t₀, ENNReal.ofReal (Real.exp (ξ * c)) =
      ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal t₀ := by
    rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  calc ENNReal.ofReal (Real.exp (ξ * c) * r)
      ≤ ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal t₀ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos (ξ * c)).le]
        exact ENNReal.ofReal_le_ofReal
          ((mul_le_mul_of_nonneg_left (hr _ hpf) (Real.exp_pos (ξ * c)).le).trans
            (mul_le_mul_of_nonneg_left hD0 (Real.exp_pos (ξ * c)).le))
    _ = ∫⁻ _ in Icc 0 t₀, ENNReal.ofReal (Real.exp (ξ * c)) := hvol.symm
    _ ≤ _ := hint

/-- A real lower bound for the set distance of the Weyl scaling, from a lower bound on its `ℝ≥0∞` values. -/
theorem le_setDist_weylScaling {D : ℂ → ℂ → ℝ} {ξ r : ℝ} {f : ℂ → ℝ} {A B : Set ℂ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hfin : ∀ u v, weylScaling D ξ f u v ≠ ⊤)
    (h : ∀ u ∈ A, ∀ v ∈ B, ENNReal.ofReal r ≤ weylScaling D ξ f u v) :
    r ≤ setDist (fun x y => (weylScaling D ξ f x y).toReal) A B := by
  unfold setDist
  refine le_csInf (hA.image2 hB) ?_
  rintro _ ⟨u, hu, v, hv, rfl⟩
  exact (ENNReal.ofReal_le_iff_le_toReal (hfin u v)).1 (h u hu v hv)

/-- Lower bound for `L_new = D_new(Q̄', ∂Q)` (paper `lem:E1`, `L_new = b_Q L`, lower half). -/
theorem setDist_weylScaling_ge_frontier {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ c : ℝ} (hξ : 0 ≤ ξ)
    {f : ℂ → ℝ} {Q Q' : Set ℂ} (hQ : closure Q' ⊆ closure Q) (hfc : ∀ z ∈ closure Q, c ≤ f z)
    (hfin : ∀ u v, weylScaling D ξ f u v ≠ ⊤) (hQ' : (closure Q').Nonempty) (hF : (frontier Q).Nonempty) :
    Real.exp (ξ * c) * setDist D (closure Q') (frontier Q) ≤
      setDist (fun x y => (weylScaling D ξ f x y).toReal) (closure Q') (frontier Q) := by
  apply le_setDist_weylScaling hQ' hF hfin
  intro u hu v hv
  have hr : ∀ w ∈ frontier Q, setDist D (closure Q') (frontier Q) ≤ D u w := fun w hw => by
    unfold setDist
    exact csInf_le ⟨0, by rintro _ ⟨a, -, b, -, rfl⟩; exact nonneg_of_isEuclideanLengthMetric hD _ _⟩
      ⟨u, hu, w, hw, rfl⟩
  exact weylScaling_ge_of_exit hD hξ hfc (hQ hu) hv.2 hr

/-- Lower bound for `a₀,new = D_new(0, ∂B_δ)` from the root bump (paper `lem:E1`, `a₀,new ≥ b D(0, ∂B_{δ/2})`). -/
theorem setDist_weylScaling_ge_sphere {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ c δ : ℝ} (hξ : 0 ≤ ξ)
    (hδ : 0 < δ) {f : ℂ → ℝ} (hfc : ∀ z ∈ closedBall (0 : ℂ) (δ / 2), c ≤ f z)
    (hfin : ∀ u v, weylScaling D ξ f u v ≠ ⊤) :
    Real.exp (ξ * c) * setDist D {0} (sphere (0 : ℂ) (δ / 2)) ≤
      setDist (fun x y => (weylScaling D ξ f x y).toReal) {0} (sphere (0 : ℂ) δ) := by
  have hr0 : δ / 2 ≠ 0 := by positivity
  have hcl : closure (ball (0 : ℂ) (δ / 2)) = closedBall 0 (δ / 2) := closure_ball 0 hr0
  have hfr : frontier (ball (0 : ℂ) (δ / 2)) = sphere (0 : ℂ) (δ / 2) := frontier_ball 0 hr0
  have hfc' : ∀ z ∈ closure (ball (0 : ℂ) (δ / 2)), c ≤ f z := by rw [hcl]; exact hfc
  have hu0 : (0 : ℂ) ∈ closure (ball (0 : ℂ) (δ / 2)) := by
    rw [hcl]; exact mem_closedBall_self (by positivity)
  have hint : ∀ x ∈ sphere (0 : ℂ) δ, x ∉ interior (ball (0 : ℂ) (δ / 2)) := by
    intro x hx h
    rw [isOpen_ball.interior_eq, mem_ball_zero_iff] at h
    rw [mem_sphere_zero_iff_norm] at hx
    linarith
  have hr' : ∀ w ∈ frontier (ball (0 : ℂ) (δ / 2)),
      setDist D {0} (sphere (0 : ℂ) (δ / 2)) ≤ D 0 w := fun w hw => by
    rw [hfr] at hw
    unfold setDist
    exact csInf_le ⟨0, by rintro _ ⟨a, -, b, -, rfl⟩; exact nonneg_of_isEuclideanLengthMetric hD _ _⟩
      ⟨0, rfl, w, hw, rfl⟩
  apply le_setDist_weylScaling (Set.singleton_nonempty _) ⟨(δ : ℂ), by simp [abs_of_pos hδ]⟩ hfin
  intro u hu v hv
  rw [Set.mem_singleton_iff] at hu
  subst hu
  exact weylScaling_ge_of_exit (Q := ball (0 : ℂ) (δ / 2)) hD hξ hfc' hu0 (hint v hv) hr'

/-- The open set `Ω_geom` of the pinch geometry (note section 2.1). -/
theorem pinchOmegaGeom_isOpen (W Q : Set ℂ) (δ : ℝ) : IsOpen (pinchOmegaGeom W Q δ) := by
  unfold pinchOmegaGeom
  exact IsOpen.connectedComponentIn (isOpen_ball.sdiff (isClosed_closure.union isClosed_closure))

/-- Upper bound for `A_new = sup_{∂B₅} D_new(0, ·; Ω_geom)` (paper `lem:E1`, `A_new ≤ b A`). If the weight
`ξ f` is at most `log b` on `Ω_geom`, the internal distances are multiplied by at most `b`. -/
theorem pinchLocalA_weylScaling_le {D : ℂ → ℂ → ℝ} {ξ b : ℝ} {f : ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ f x y).toReal)) (hb : 0 < b)
    (hfin : ∀ u v, weylScaling D ξ f u v ≠ ⊤) (W Q : Set ℂ) (δ : ℝ)
    (hweight : ∀ z ∈ pinchOmegaGeom W Q δ, ξ * f z ≤ Real.log b) :
    pinchLocalA (fun x y => (weylScaling D ξ f x y).toReal) W Q δ ≤
      ENNReal.ofReal b * pinchLocalA D W Q δ := by
  unfold pinchLocalA
  simp only [ENNReal.mul_iSup]
  refine iSup₂_le fun x hx => ?_
  have key := hD.internalMetric_weylScaling_le hE (fun x y => ENNReal.toReal_nonneg)
    (pinchOmegaGeom_isOpen W Q δ) (hD.weylScaling_zero ξ)
    (fun x y => ENNReal.ofReal_toReal (hfin x y)) hweight 0 x
  rw [Real.exp_log hb] at key
  refine key.trans ?_
  exact le_iSup₂ (f := fun (x : ℂ) (_ : x ∈ sphere (0 : ℂ) 5) =>
    ENNReal.ofReal b * internalMetric D (pinchOmegaGeom W Q δ) 0 x) x hx

end HarmonicBalls.S11m.E1Bounds
