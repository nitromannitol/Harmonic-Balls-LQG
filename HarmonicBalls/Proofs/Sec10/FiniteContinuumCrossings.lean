import HarmonicBalls.Proofs.Sec10.NestedContinuumCrossing

/-!
# Finite families of annular components

If only finitely many components of a compact continuum cross one fixed
interior annulus, one component crosses the original annulus. The finiteness
assumption remains a separate hypothesis.
-/

namespace HarmonicBalls

open Metric Set Topology Filter

/-- Finitely many components crossing an interior annulus suffice to select
one component crossing both original boundary circles. -/
theorem IsConnected.exists_annular_component_crossing_of_finite
    {K : Set ℂ} (hK : IsConnected K) (hKcompact : IsCompact K)
    (w : ℂ) {r R : ℝ} (hrR : r < R) (hcross : CrossesAnnulus K w r R)
    (hfinite : (crossingComponents (K ∩ annulus w r R) w
      (r + (R - r) / 3) (R - (R - r) / 3)).Finite) :
    (crossingComponents (K ∩ annulus w r R) w r R).Nonempty := by
  let a : ℕ → ℝ := fun n => r + ((R - r) / 4) * (1 / ((n : ℝ) + 1))
  let b : ℕ → ℝ := fun n => R - ((R - r) / 4) * (1 / ((n : ℝ) + 1))
  have hq (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).2 (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hbounds (n : ℕ) : r < a n ∧ a n < r + (R-r)/3 ∧
      r + (R-r)/3 < R - (R-r)/3 ∧ R - (R-r)/3 < b n ∧ b n < R := by
    have hp : 0 < R-r := sub_pos.mpr hrR
    have hmult : ((R-r)/4) * (1 / ((n : ℝ) + 1)) ≤ (R-r)/4 := by
      nlinarith [(hq n).2]
    have hpos : 0 < ((R-r)/4) * (1 / ((n : ℝ) + 1)) := by positivity
    dsimp [a, b]
    constructor <;> [skip; constructor <;> [skip; constructor <;> [skip; constructor]]] <;> linarith
  have hex (n : ℕ) : ∃ D ∈ crossingComponents (K ∩ annulus w r R) w
      (r + (R-r)/3) (R - (R-r)/3), CrossesAnnulus D w (a n) (b n) := by
    have hb := hbounds n
    obtain ⟨D, hD, hcrossD⟩ := IsConnected.exists_annular_component_crossing_smaller hK hKcompact w
      hb.1 (by linarith [hb.2.1, hb.2.2.1, hb.2.2.2.1]) hb.2.2.2.2 hcross
    have hconn : IsPreconnected D := by
      obtain ⟨x, hx, rfl⟩ := hD
      exact isPreconnected_connectedComponentIn
    obtain ⟨x, hxD, hx⟩ := IsPreconnected.exists_mem_sphere_of_crosses hconn hb.2.1
      (by linarith [hb.2.2.1, hb.2.2.2.1]) hcrossD
    obtain ⟨y, hyD, hy⟩ := IsPreconnected.exists_mem_sphere_of_crosses hconn
      (by linarith [hb.2.1, hb.2.2.1]) hb.2.2.2.1 hcrossD
    exact ⟨D, ⟨hD, ⟨⟨x, subset_closure hxD, hx⟩, ⟨y, subset_closure hyD, hy⟩⟩⟩, hcrossD⟩
  have hfreq : ∃ᶠ n : ℕ in atTop, ∃ D ∈ crossingComponents (K ∩ annulus w r R) w
      (r + (R-r)/3) (R - (R-r)/3), CrossesAnnulus D w (a n) (b n) :=
    (Eventually.of_forall hex).frequently
  obtain ⟨D, hD, hDfreq⟩ := hfinite.frequently_exists.mp hfreq
  have hDsub : D ⊆ K := by
    obtain ⟨x, hx, rfl⟩ := hD.1
    exact (connectedComponentIn_subset _ x).trans inter_subset_left
  have hcompact : IsCompact (closure D) := hKcompact.of_isClosed_subset isClosed_closure
    (closure_minimal hDsub hKcompact.isClosed)
  have hclosed : IsClosed ((fun z : ℂ => dist z w) '' closure D) :=
    (hcompact.image (continuous_id.dist continuous_const)).isClosed
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have halim : Tendsto a atTop (𝓝 r) := by
    simpa [a] using tendsto_const_nhds.add (tendsto_const_nhds.mul hlim)
  have hblim : Tendsto b atTop (𝓝 R) := by
    simpa [b] using tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim)
  have hamem : r ∈ (fun z : ℂ => dist z w) '' closure D :=
    hclosed.mem_of_frequently_of_tendsto (hDfreq.mono fun n hn => by
      obtain ⟨⟨x, hx, hxa⟩, _⟩ := hn
      exact ⟨x, hx, mem_sphere.mp hxa⟩) halim
  have hbmem : R ∈ (fun z : ℂ => dist z w) '' closure D :=
    hclosed.mem_of_frequently_of_tendsto (hDfreq.mono fun n hn => by
      obtain ⟨_, ⟨x, hx, hxb⟩⟩ := hn
      exact ⟨x, hx, mem_sphere.mp hxb⟩) hblim
  obtain ⟨x, hx, hxr⟩ := hamem
  obtain ⟨y, hy, hyR⟩ := hbmem
  exact ⟨D, hD.1, ⟨⟨x, hx, mem_sphere.mpr hxr⟩, ⟨y, hy, mem_sphere.mpr hyR⟩⟩⟩

end HarmonicBalls
