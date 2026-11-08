import HarmonicBalls.Defs.LQGGraphDistance

/-!
# Complex similarity covariance of Liouville graph distance

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

private theorem complex_similarity_ball (r : ℂ) (hr : r ≠ 0) (b a : ℂ) (s : ℝ) :
    (fun x : ℂ => r * x + b) '' Metric.ball a s =
      Metric.ball (r * a + b) (‖r‖ * s) := by
  have h := Metric.smul_image_ball hr a s
  have ht : (fun x : ℂ => x + b) '' Metric.ball (r • a) (‖r‖ * s) =
      Metric.ball (r • a + b) (‖r‖ * s) := by
    ext x
    simp only [mem_image, Metric.mem_ball]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [dist_add_right] using hy
    · intro hx
      refine ⟨x - b, ?_, sub_add_cancel x b⟩
      have hd : dist (x - b) (r • a) = dist x (r • a + b) := by
        simpa only [sub_add_cancel] using (dist_add_right (x - b) (r • a) b).symm
      rwa [hd]
  rw [← h] at ht
  simpa only [Set.image_image, Function.comp_def, smul_eq_mul] using ht

/-- The admissible cover counts are invariant under a nonzero complex similarity. -/
theorem isLiouvilleGraphCover_complex_similarity_iff (μ : Measure ℂ) (ε : ℝ) (z w : ℂ)
    (n : ℕ) (r : ℂ) (hr : r ≠ 0) (b : ℂ) :
    IsLiouvilleGraphCover (μ.map (fun x => r * x + b)) ε
      (r * z + b) (r * w + b) n ↔
      IsLiouvilleGraphCover μ ε z w n := by
  let f : ℂ → ℂ := fun x => r * x + b
  let g : ℂ → ℂ := fun x => r⁻¹ * x + (-r⁻¹ * b)
  have hrC : r ≠ 0 := hr
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
      ‖r⁻¹‖ (norm_pos_iff.mpr (inv_ne_zero hr)) (by simpa only [g] using
        (complex_similarity_ball r⁻¹ (inv_ne_zero hr) (-r⁻¹ * b))) h
    have hgfid : g ∘ f = id := funext hgf
    rw [Measure.map_map hg.measurable hf.measurable, hgfid, Measure.map_id] at hh
    simpa only [hgf] using hh
  · intro h
    exact cover_map_of_similarity μ ε z w n f hf hinjf ‖r‖ (norm_pos_iff.mpr hr)
      (complex_similarity_ball r hr b) h

/-- Exact graph-distance covariance, including the infinite case. -/
theorem liouvilleGraphDistance_complex_similarity (μ : Measure ℂ) (ε : ℝ) (z w : ℂ)
    (r : ℂ) (hr : r ≠ 0) (b : ℂ) :
    liouvilleGraphDistance (μ.map (fun x => r * x + b)) ε
      (r * z + b) (r * w + b) = liouvilleGraphDistance μ ε z w := by
  unfold liouvilleGraphDistance
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq, isLiouvilleGraphCover_complex_similarity_iff μ ε z w _ r hr b]

/-- The point-to-point graph dimension is preserved by a nonzero complex similarity. -/
theorem isLiouvilleGraphDimension_complex_similarity_iff (μ : Measure ℂ) (z w : ℂ) (d : ℝ) (r : ℂ)
    (hr : r ≠ 0) (b : ℂ) :
    IsLiouvilleGraphDimension (μ.map (fun x => r * x + b))
      (r * z + b) (r * w + b) d ↔
      IsLiouvilleGraphDimension μ z w d := by
  have he : liouvilleGraphExponent (μ.map (fun x => r * x + b))
      (r * z + b) (r * w + b) = liouvilleGraphExponent μ z w := by
    funext n
    unfold liouvilleGraphExponent
    rw [liouvilleGraphDistance_complex_similarity μ _ z w r hr b]
  simp only [IsLiouvilleGraphDimension, he,
    liouvilleGraphDistance_complex_similarity μ _ z w r hr b]

#print axioms isLiouvilleGraphCover_complex_similarity_iff
#print axioms liouvilleGraphDistance_complex_similarity
#print axioms isLiouvilleGraphDimension_complex_similarity_iff

end HarmonicBalls
