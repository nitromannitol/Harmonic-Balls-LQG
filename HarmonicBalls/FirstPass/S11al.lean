import HarmonicBalls.FirstPass.S11i.Certificate

/-!
# Locality of the common certificate (Lemma 11.13; blocker (a) of n4)

`CertificateEvent μ D …` (`FirstPass/S11i/Certificate.lean:42`) depends on the length metric `D` only through the
internal metrics `internalMetric D U` on the domains `U` below and the set distances `setDist D A B`. Each of these
reads `D` only on pairs of points of a fixed domain, namely:

* `internalMetric D (rescaledSet Ostar r z) z x`, for `x ∈ sphere z (5r)`;
* `internalDiam D (r η) A` for `A = rescaledSet K r z`, `K ∈ {certK0, certK1, certK2}`, whose domain is
  `thickening (r η) A`;
* `setDist D A B` for `A, B` contained in `closedBall z (7r)`.

Under the buffered containments of `CertificateContainments` (scale one, in `B_7 = closedBall 0 7`), all these domains
and sets lie in `closedBall z (7r)`. Hence `CertificateEvent μ D` and `CertificateEvent μ D'` agree whenever
`D = D'` on `closedBall z (7r) ×ˢ closedBall z (7r)` (`certificateEvent_congr_of_eqOn_closedBall`).

The measure-theoretic term `μ (rescaledSet U r z)` and `annulusGreenPotentialSup μ z (3r) (6r)` do not involve `D`,
so the containment of `U` is not needed for locality and is not recorded.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace FirstPassS11i

open HarmonicBalls

/-- The buffered containments of Lemma 11.13 in scale one (`B_7 = closedBall 0 7`), for the sets `Ostar`, `Q'`, `Q`,
`V`, `W`, `T` and the buffer `η`. Each field is used by the locality argument only in the form stated; the fields are
hypotheses (the buffered path-domain properties of the construction, `notes/fp-gaps/CHATGPT-n3-Q1-eq34.md` §5, Step 1):
* `Ostar_sub`: the domain `O_*` lies in `B_7` (its rescaled copies lie in `closedBall z (7r)`);
* `Qprime_sub`, `Q_sub`: the clearance sets `Q'`, `Q` lie in `B_7` (`closure`, `frontier` of their rescalings then lie in
  `closedBall z (7r)` since the balls are closed);
* `T_thick`, `V_thick`, `W_thick`: the buffered sets `T`, `V`, `W` lie in `B_7` after thickening by `η`, `η`, `4η`,
  which covers `K₀ = closure (T \ B_{3η}(W))`, `K₁ = closure V`, `K₂ = closure (B_{3η}(W) \ V)` and their `η`-buffers;
* `three_eta_le`, `eta_pos`: the buffer satisfies `0 < η` and `3η ≤ 7`, so the spheres `∂B_{rη}`, `∂B_{2rη}`,
  `∂B_{3rη}` lie in `closedBall z (7r)`. -/
structure CertificateContainments (η : ℝ) (Ostar V W T Q' Q : Set ℂ) : Prop where
  eta_pos : 0 < η
  three_eta_le : 3 * η ≤ 7
  Ostar_sub : Ostar ⊆ closedBall 0 7
  Qprime_sub : Q' ⊆ closedBall 0 7
  Q_sub : Q ⊆ closedBall 0 7
  T_thick : thickening η T ⊆ closedBall 0 7
  V_thick : thickening η V ⊆ closedBall 0 7
  W_thick : thickening (4 * η) W ⊆ closedBall 0 7

/-- The buffer of `K₀` lies in the buffer of `T`: `thickening η (closure (T \ B_{3η}(W))) = thickening η (T \ …) ⊆
thickening η T`. -/
lemma thickening_certK0_subset {η : ℝ} {T W : Set ℂ} {R : ℝ} (hT : thickening η T ⊆ closedBall 0 R) :
    thickening η (certK0 T W η) ⊆ closedBall 0 R := by
  unfold certK0
  rw [thickening_closure]
  exact (thickening_subset_of_subset η Set.sdiff_subset).trans hT

/-- The buffer of `K₁ = closure V` is the buffer of `V`. -/
lemma thickening_certK1_subset {η : ℝ} {V : Set ℂ} {R : ℝ} (hV : thickening η V ⊆ closedBall 0 R) :
    thickening η (certK1 V) ⊆ closedBall 0 R := by
  unfold certK1
  rw [thickening_closure]
  exact hV

/-- The buffer of `K₂ = closure (B_{3η}(W) \ V)` lies in the `4η`-buffer of `W`. -/
lemma thickening_certK2_subset {η : ℝ} {V W : Set ℂ} {R : ℝ} (hW : thickening (4 * η) W ⊆ closedBall 0 R) :
    thickening η (certK2 V W η) ⊆ closedBall 0 R := by
  unfold certK2
  rw [thickening_closure]
  exact (thickening_subset_of_subset η Set.sdiff_subset).trans
    ((thickening_thickening_subset η (3 * η) W).trans ((thickening_mono (by linarith) W).trans hW))

/-- A scale-one set in `closedBall 0 R` rescales into `closedBall z (R r)`, for `r ≥ 0`. -/
lemma rescaledSet_subset_closedBall' {S : Set ℂ} {R r : ℝ} {z : ℂ} (hr : 0 ≤ r) (hS : S ⊆ closedBall 0 R) :
    rescaledSet S r z ⊆ closedBall z (R * r) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp (hS hx)
  show (r : ℂ) * x + z ∈ closedBall z (R * r)
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_left hx' hr).trans_eq (mul_comm _ _)

/-- The `η`-buffer of a rescaled set lies in `closedBall z (R r)` when the scale-one `η`-buffer lies in `closedBall 0 R`:
`thickening (r η) (rescaledSet K r z) ⊆ closedBall z (R r)`, for `r > 0`. -/
lemma thickening_rescaledSet_subset_closedBall {K : Set ℂ} {R η r : ℝ} {z : ℂ} (hr : 0 < r)
    (hK : thickening η K ⊆ closedBall 0 R) :
    thickening (r * η) (rescaledSet K r z) ⊆ closedBall z (R * r) := by
  intro x hx
  obtain ⟨k, ⟨k₀, hk₀, hkdef⟩, hxk⟩ := mem_thickening_iff.mp hx
  subst hkdef
  dsimp only at hxk
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hinv : (r : ℂ)⁻¹ * ((r : ℂ) * k₀) = k₀ := by
    rw [← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
  have hyK : (r : ℂ)⁻¹ * (x - z) ∈ thickening η K := by
    refine mem_thickening_iff.mpr ⟨k₀, hk₀, ?_⟩
    have e : (r : ℂ)⁻¹ * (x - z) - k₀ = (r : ℂ)⁻¹ * (x - ((r : ℂ) * k₀ + z)) := by
      linear_combination hinv
    rw [dist_eq_norm, e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le, ← dist_eq_norm,
      inv_mul_lt_iff₀ hr]
    exact hxk
  have hyB := hK hyK
  rw [mem_closedBall, dist_zero_right] at hyB
  rw [mem_closedBall, dist_eq_norm]
  have hxz : x - z = (r : ℂ) * ((r : ℂ)⁻¹ * (x - z)) := (mul_inv_cancel_left₀ hr0 _).symm
  rw [hxz, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  exact (mul_le_mul_of_nonneg_left hyB hr.le).trans_eq (mul_comm _ _)

/-- Curve length on `[0,1]`: if the curve stays in `U ⊆ B` then `D` is read only on `B × B`. -/
lemma pathLength_congr_of_subset {D D' : ℂ → ℂ → ℝ} {U B : Set ℂ} (hUB : U ⊆ B)
    (hEq : ∀ x ∈ B, ∀ y ∈ B, D x y = D' x y) {z w : ℂ} (P : Path z w) (hP : ∀ t, P t ∈ U) :
    pathLength D P = pathLength D' P := by
  unfold pathLength curveLength
  refine iSup_congr fun q => Finset.sum_congr rfl fun i _ => ?_
  have key : ∀ j, P.extend (q.2.1 j) ∈ B := by
    intro j
    have hj : q.2.1 j ∈ Icc (0 : ℝ) 1 := q.2.2.2 j
    have e : P.extend (q.2.1 j) = P ⟨q.2.1 j, hj⟩ := Path.extend_extends' P ⟨q.2.1 j, hj⟩
    rw [e]
    exact hUB (hP _)
  exact congrArg ENNReal.ofReal (hEq _ (key (i + 1)) _ (key i))

/-- The internal metric `D(z, w; U)` reads `D` only on `B × B` when `U ⊆ B`. -/
lemma internalMetric_congr_of_subset {D D' : ℂ → ℂ → ℝ} {U B : Set ℂ} (hUB : U ⊆ B)
    (hEq : ∀ x ∈ B, ∀ y ∈ B, D x y = D' x y) (z w : ℂ) :
    internalMetric D U z w = internalMetric D' U z w := by
  unfold internalMetric
  refine iInf_congr fun P => ?_
  by_cases hP : ∀ t, P t ∈ U
  · rw [iInf_pos hP, iInf_pos hP]
    exact pathLength_congr_of_subset hUB hEq P hP
  · rw [iInf_neg hP, iInf_neg hP]

/-- The set distance `D(A, A') = inf {D x y}` reads `D` only on `B × B` when `A, A' ⊆ B`. -/
lemma setDist_congr_of_subset {D D' : ℂ → ℂ → ℝ} {A A' B : Set ℂ} (hA : A ⊆ B) (hA' : A' ⊆ B)
    (hEq : ∀ x ∈ B, ∀ y ∈ B, D x y = D' x y) : setDist D A A' = setDist D' A A' := by
  unfold setDist
  congr 1
  ext t
  simp only [Set.mem_image2]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, (hEq a (hA ha) b (hA' hb)).symm⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, hEq a (hA ha) b (hA' hb)⟩

/-- The internal diameter `diam^δ(A) = sup_{x,y ∈ A} D(x, y; B_δ(A))` reads `D` only on `B × B` when `B_δ(A) ⊆ B`. -/
lemma internalDiam_congr_of_subset {D D' : ℂ → ℂ → ℝ} {δ : ℝ} {A B : Set ℂ} (hU : thickening δ A ⊆ B)
    (hEq : ∀ x ∈ B, ∀ y ∈ B, D x y = D' x y) : internalDiam D δ A = internalDiam D' δ A := by
  unfold internalDiam
  exact iSup_congr fun x => iSup_congr fun _ => iSup_congr fun y => iSup_congr fun _ =>
    internalMetric_congr_of_subset hU hEq x y

/-- **Locality of the common certificate (Lemma 11.13, step 2; n4 blocker (a)).** Under the buffered containments
`CertificateContainments η Ostar V W T Q' Q` in `B_7`, the certificate event at centre `z` and radius `r > 0` is
unchanged when the length metric is changed on `closedBall z (7r) ×ˢ closedBall z (7r)`. -/
theorem certificateEvent_congr_of_eqOn_closedBall {μ : Measure ℂ} {D D' : ℂ → ℂ → ℝ}
    {Ostar U V W T Q' Q : Set ℂ} {η M r : ℝ} {z : ℂ}
    (hC : CertificateContainments η Ostar V W T Q' Q) (hr : 0 < r)
    (hEq : Set.EqOn (Function.uncurry D) (Function.uncurry D') (closedBall z (7 * r) ×ˢ closedBall z (7 * r))) :
    CertificateEvent μ D Ostar U V W T Q' Q η M r z ↔ CertificateEvent μ D' Ostar U V W T Q' Q η M r z := by
  have hB : ∀ x ∈ closedBall z (7 * r), ∀ y ∈ closedBall z (7 * r), D x y = D' x y :=
    fun x hx y hy => hEq (Set.mk_mem_prod hx hy)
  have hO : rescaledSet Ostar r z ⊆ closedBall z (7 * r) :=
    rescaledSet_subset_closedBall' hr.le hC.Ostar_sub
  have hQ' : closure (rescaledSet Q' r z) ⊆ closedBall z (7 * r) :=
    closure_minimal (rescaledSet_subset_closedBall' hr.le hC.Qprime_sub) isClosed_closedBall
  have hfQ : frontier (rescaledSet Q r z) ⊆ closedBall z (7 * r) :=
    frontier_subset_closure.trans
      (closure_minimal (rescaledSet_subset_closedBall' hr.le hC.Q_sub) isClosed_closedBall)
  have hK0 : thickening (r * η) (rescaledSet (certK0 T W η) r z) ⊆ closedBall z (7 * r) :=
    thickening_rescaledSet_subset_closedBall hr (thickening_certK0_subset hC.T_thick)
  have hK1 : thickening (r * η) (rescaledSet (certK1 V) r z) ⊆ closedBall z (7 * r) :=
    thickening_rescaledSet_subset_closedBall hr (thickening_certK1_subset hC.V_thick)
  have hK2 : thickening (r * η) (rescaledSet (certK2 V W η) r z) ⊆ closedBall z (7 * r) :=
    thickening_rescaledSet_subset_closedBall hr (thickening_certK2_subset hC.W_thick)
  have hz : ({z} : Set ℂ) ⊆ closedBall z (7 * r) :=
    singleton_subset_iff.mpr (mem_closedBall_self (by positivity))
  have h1 : r * η ≤ 7 * r := by nlinarith [hC.eta_pos, hC.three_eta_le, hr]
  have h2 : 2 * r * η ≤ 7 * r := by nlinarith [hC.eta_pos, hC.three_eta_le, hr]
  have h3 : 3 * r * η ≤ 7 * r := by nlinarith [hC.eta_pos, hC.three_eta_le, hr]
  have sph1 : sphere z (r * η) ⊆ closedBall z (7 * r) :=
    sphere_subset_closedBall.trans (closedBall_subset_closedBall h1)
  have sph2 : sphere z (2 * r * η) ⊆ closedBall z (7 * r) :=
    sphere_subset_closedBall.trans (closedBall_subset_closedBall h2)
  have sph3 : sphere z (3 * r * η) ⊆ closedBall z (7 * r) :=
    sphere_subset_closedBall.trans (closedBall_subset_closedBall h3)
  have e1 : (⨆ x ∈ sphere z (5 * r), internalMetric D (rescaledSet Ostar r z) z x) =
      ⨆ x ∈ sphere z (5 * r), internalMetric D' (rescaledSet Ostar r z) z x :=
    iSup_congr fun x => iSup_congr fun _ => internalMetric_congr_of_subset hO hB z x
  have e2 : setDist D (closure (rescaledSet Q' r z)) (frontier (rescaledSet Q r z)) =
      setDist D' (closure (rescaledSet Q' r z)) (frontier (rescaledSet Q r z)) :=
    setDist_congr_of_subset hQ' hfQ hB
  have e3 : internalDiam D (r * η) (rescaledSet (certK0 T W η) r z) =
      internalDiam D' (r * η) (rescaledSet (certK0 T W η) r z) :=
    internalDiam_congr_of_subset hK0 hB
  have e4 : setDist D {z} (sphere z (r * η)) = setDist D' {z} (sphere z (r * η)) :=
    setDist_congr_of_subset hz sph1 hB
  have e5 : internalDiam D (r * η) (rescaledSet (certK1 V) r z) =
      internalDiam D' (r * η) (rescaledSet (certK1 V) r z) :=
    internalDiam_congr_of_subset hK1 hB
  have e6 : setDist D (sphere z (r * η)) (sphere z (2 * r * η)) =
      setDist D' (sphere z (r * η)) (sphere z (2 * r * η)) :=
    setDist_congr_of_subset sph1 sph2 hB
  have e7 : internalDiam D (r * η) (rescaledSet (certK2 V W η) r z) =
      internalDiam D' (r * η) (rescaledSet (certK2 V W η) r z) :=
    internalDiam_congr_of_subset hK2 hB
  have e8 : setDist D (sphere z (2 * r * η)) (sphere z (3 * r * η)) =
      setDist D' (sphere z (2 * r * η)) (sphere z (3 * r * η)) :=
    setDist_congr_of_subset sph2 sph3 hB
  unfold CertificateEvent
  rw [e1, e2, e3, e4, e5, e6, e7, e8]

end FirstPassS11i

#print axioms FirstPassS11i.certificateEvent_congr_of_eqOn_closedBall
#print axioms FirstPassS11i.thickening_rescaledSet_subset_closedBall
