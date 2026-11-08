import HarmonicBalls.Defs.LQGGraphDistance

/-!
# Affine covariance of Liouville graph distance

We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

private theorem cover_map_of_similarity (μ : Measure ℂ) (ε : ℝ) (z w : ℂ)
    (n : ℕ) (f : ℂ → ℂ) (hf : Continuous f) (hinj : Function.Injective f)
    (c : ℝ) (hc : 0 < c)
    (hball : ∀ a s, f '' Metric.ball a s = Metric.ball (f a) (c * s))
    (h : IsLiouvilleGraphCover μ ε z w n) :
    IsLiouvilleGraphCover (μ.map f) ε (f z) (f w) n := by
  obtain ⟨balls, hb, p, hp⟩ := h
  refine ⟨fun i => (f (balls i).1, c * (balls i).2), ?_, p.map hf, ?_⟩
  · intro i
    refine ⟨mul_pos hc (hb i).1, ?_⟩
    rw [Measure.map_apply hf.measurable Metric.isOpen_ball.measurableSet,
      ← hball, Set.preimage_image_eq _ hinj]
    exact (hb i).2
  · intro t
    obtain ⟨i, hi⟩ := hp t
    refine ⟨i, ?_⟩
    rw [← hball]
    exact ⟨p t, hi, rfl⟩

private theorem affine_ball (r : ℝ) (hr : r ≠ 0) (b a : ℂ) (s : ℝ) :
    (fun x : ℂ => (r : ℂ) * x + b) '' Metric.ball a s =
      Metric.ball ((r : ℂ) * a + b) (|r| * s) := by
  have h := Metric.smul_image_ball (show (r : ℂ) ≠ 0 by exact_mod_cast hr) a s
  have ht : (fun x : ℂ => x + b) '' Metric.ball ((r : ℂ) • a) (‖(r : ℂ)‖ * s) =
      Metric.ball ((r : ℂ) • a + b) (‖(r : ℂ)‖ * s) := by
    ext x
    simp only [mem_image, Metric.mem_ball]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [dist_add_right] using hy
    · intro hx
      refine ⟨x - b, ?_, sub_add_cancel x b⟩
      have hd : dist (x - b) ((r : ℂ) • a) = dist x ((r : ℂ) • a + b) := by
        simpa only [sub_add_cancel] using (dist_add_right (x - b) ((r : ℂ) • a) b).symm
      rwa [hd]
  rw [← h] at ht
  simpa only [Set.image_image, Function.comp_def, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs] using ht

/-- The admissible cover counts are invariant under a nonzero real similarity. -/
theorem isLiouvilleGraphCover_affine_iff (μ : Measure ℂ) (ε : ℝ) (z w : ℂ)
    (n : ℕ) (r : ℝ) (hr : r ≠ 0) (b : ℂ) :
    IsLiouvilleGraphCover (μ.map (fun x => (r : ℂ) * x + b)) ε
      ((r : ℂ) * z + b) ((r : ℂ) * w + b) n ↔
      IsLiouvilleGraphCover μ ε z w n := by
  let f : ℂ → ℂ := fun x => (r : ℂ) * x + b
  let g : ℂ → ℂ := fun x => (r⁻¹ : ℂ) * x + (-(r⁻¹ : ℂ) * b)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hgf : ∀ x, g (f x) = x := by
    intro x
    dsimp [f, g]
    field_simp
    ring
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hinjf : Function.Injective f := Function.LeftInverse.injective hgf
  have hfg : ∀ x, f (g x) = x := by
    intro x
    dsimp [f, g]
    field_simp
    ring
  have hinjg : Function.Injective g := Function.LeftInverse.injective hfg
  constructor
  · intro h
    have hh := cover_map_of_similarity (μ.map f) ε (f z) (f w) n g hg hinjg
      |r⁻¹| (abs_pos.mpr (inv_ne_zero hr)) (by simpa only [g, Complex.ofReal_inv] using
        (affine_ball r⁻¹ (inv_ne_zero hr) (-(r⁻¹ : ℂ) * b))) h
    have hgfid : g ∘ f = id := funext hgf
    rw [Measure.map_map hg.measurable hf.measurable, hgfid, Measure.map_id] at hh
    simpa only [hgf] using hh
  · intro h
    exact cover_map_of_similarity μ ε z w n f hf hinjf |r| (abs_pos.mpr hr)
      (affine_ball r hr b) h

/-- Exact graph-distance covariance, including the infinite case. -/
theorem liouvilleGraphDistance_affine (μ : Measure ℂ) (ε : ℝ) (z w : ℂ)
    (r : ℝ) (hr : r ≠ 0) (b : ℂ) :
    liouvilleGraphDistance (μ.map (fun x => (r : ℂ) * x + b)) ε
      ((r : ℂ) * z + b) ((r : ℂ) * w + b) = liouvilleGraphDistance μ ε z w := by
  unfold liouvilleGraphDistance
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq, isLiouvilleGraphCover_affine_iff μ ε z w _ r hr b]

/-- The point-to-point graph dimension is preserved by a nonzero real similarity. -/
theorem isLiouvilleGraphDimension_affine_iff (μ : Measure ℂ) (z w : ℂ) (d r : ℝ)
    (hr : r ≠ 0) (b : ℂ) :
    IsLiouvilleGraphDimension (μ.map (fun x => (r : ℂ) * x + b))
      ((r : ℂ) * z + b) ((r : ℂ) * w + b) d ↔
      IsLiouvilleGraphDimension μ z w d := by
  have he : liouvilleGraphExponent (μ.map (fun x => (r : ℂ) * x + b))
      ((r : ℂ) * z + b) ((r : ℂ) * w + b) = liouvilleGraphExponent μ z w := by
    funext n
    unfold liouvilleGraphExponent
    rw [liouvilleGraphDistance_affine μ _ z w r hr b]
  simp only [IsLiouvilleGraphDimension, he,
    liouvilleGraphDistance_affine μ _ z w r hr b]

#print axioms isLiouvilleGraphCover_affine_iff
#print axioms liouvilleGraphDistance_affine
#print axioms isLiouvilleGraphDimension_affine_iff

end HarmonicBalls
