import HarmonicBalls.Steps.Sec11.ConeCoordinates

/-! # Cones adapted to Lipschitz graphs -/

namespace HarmonicBalls

open Complex Set Topology

/-- The open wedge above a Lipschitz graph of slope at most `k` is an open cone. -/
theorem isOpenCone_verticalWedge {k : ℝ} (hk : 0 < k) :
    IsOpenCone {x : ℂ | k * |x.re| < x.im} := by
  let v : ℂ := 1 + (k : ℂ) * I
  let w : ℂ := -1 + (k : ℂ) * I
  have hvw : 0 < planarCross v w := by
    simp [planarCross, v, w]
    linarith
  have heq : {x : ℂ | k * |x.re| < x.im} = openSector v w := by
    ext x
    rw [mem_openSector_iff_planarCross_pos hvw]
    simp only [mem_ofPred_eq, planarCross, v, w, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
    rcases le_total 0 x.re with h | h
    · rw [abs_of_nonneg h]
      constructor
      · intro hx; constructor <;> nlinarith [mul_nonneg hk.le h]
      · rintro ⟨h1, h2⟩; nlinarith
    · rw [abs_of_nonpos h]
      constructor
      · intro hx; constructor <;> nlinarith [mul_nonpos_of_nonneg_of_nonpos hk.le h]
      · rintro ⟨h1, h2⟩; nlinarith
  rw [heq]
  exact isOpenCone_openSector_of_planarCross_pos hvw

/-- Real linear isometries preserve proper open cones. -/
theorem IsOpenCone.linearIsometry_image {Q : Set ℂ} (hQ : IsOpenCone Q)
    (e : ℂ ≃ₗᵢ[ℝ] ℂ) : IsOpenCone (e '' Q) := by
  obtain ⟨hne, hopen, hproper, v, w, hv, hw, hsector⟩ := hQ
  refine ⟨hne.image e, ?_, ?_, e v, e w, ?_, ?_, ?_⟩
  · exact e.toHomeomorph.isOpenMap Q hopen
  · intro hall
    apply hproper
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hx : e x ∈ e '' Q := by rw [hall]; trivial
      obtain ⟨y, hy, heq⟩ := hx
      exact e.injective heq ▸ hy
  · exact fun heq => hv (e.injective (by simpa using heq))
  · exact fun heq => hw (e.injective (by simpa using heq))
  · rw [hsector]
    ext x
    constructor
    · rintro ⟨y, ⟨a, b, ha, hb, rfl⟩, rfl⟩
      exact ⟨a, b, ha, hb, by rw [map_add, map_smul, map_smul]⟩
    · rintro ⟨a, b, ha, hb, hx⟩
      refine ⟨a • v + b • w, ⟨a, b, ha, hb, rfl⟩, ?_⟩
      rw [map_add, map_smul, map_smul]
      exact hx.symm

end HarmonicBalls
