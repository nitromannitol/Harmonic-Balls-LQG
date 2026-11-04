import HarmonicBalls.Proofs.Sec5.FiniteRankPointRemoval
import HarmonicBalls.Proofs.Sec5.AccumulationDiscCompatibility

/-! # Barrier covers for finite-rank point sets -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian

/-- Local finiteness of finite rank passes to subsets. -/
theorem LocallyFiniteRank.mono {U K K' : Set ℂ} {n : ℕ}
    (hK : LocallyFiniteRank U n K) (hsub : K' ⊆ K) : LocallyFiniteRank U n K' := by
  induction n generalizing K K' with
  | zero =>
    intro C hC hCU
    exact (hK C hC hCU).subset (inter_subset_inter_left C hsub)
  | succ n ih =>
    obtain ⟨L, hLc, hL, hK⟩ := hK
    refine ⟨L, hLc, hL, ?_⟩
    intro C hC hCU
    exact (hK C hC hCU).subset (inter_subset_inter_left C hsub)

/-- Finite sets admit a continuous nonnegative capped Green barrier that is
small at a point outside the set and strictly above a given level on it. -/
theorem exists_capped_barrier_of_finite {R M ε : ℝ} {J : Finset ℂ} {x : ℂ}
    (hJ : (J : Set ℂ) ⊆ ball (0 : ℂ) R) (hx : x ∉ J)
    (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ b : ℂ → ℝ, ContinuousOn b (closedBall (0 : ℂ) R) ∧
      LaplacianLE b 0 (ball (0 : ℂ) R) ∧ (∀ y, 0 ≤ b y) ∧ b x < ε ∧
      ∀ y ∈ J, M < b y := by
  classical
  obtain ⟨c, hc, W, hW, hJW, hsmall, hcover⟩ :=
    exists_finset_cappedGreenBarrier_neighborhood J hJ hx hM hε
  let b : ℂ → ℝ := fun y => ∑ a ∈ J, cappedGreenBarrier R a c (M + 1) y
  refine ⟨b, continuousOn_finsetSum J (fun a ha => continuousOn_cappedGreenBarrier (hJ ha) hc),
    ?_, ?_, hsmall, fun y hy => hcover y (hJW hy)⟩
  · have h := (laplacianLE_zero (0 : Measure ℂ) (ball (0 : ℂ) R)).add_finset_of_nonpos J
      (b := fun a => cappedGreenBarrier R a c (M + 1))
      (fun a ha => laplacianLE_cappedGreenBarrier (hJ ha) hc)
    simpa [b] using h
  · intro y
    exact Finset.sum_nonneg fun a _ => cappedGreenBarrier_nonneg hc.le (by linarith)

/-- Any compact portion of a closed finite-rank locally finite set admits a
continuous nonnegative barrier, arbitrarily small at any point outside it. -/
theorem exists_capped_barrier_of_locallyFiniteRank
    {R M ε : ℝ} {K C : Set ℂ} {x : ℂ} {n : ℕ}
    (hKc : IsClosed K) (hK : LocallyFiniteRank (ball (0 : ℂ) R) n K)
    (hC : IsCompact C) (hCU : C ⊆ ball (0 : ℂ) R)
    (hxK : x ∉ K) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ b : ℂ → ℝ, ContinuousOn b (closedBall (0 : ℂ) R) ∧
      LaplacianLE b 0 (ball (0 : ℂ) R) ∧ (∀ y, 0 ≤ b y) ∧ b x < ε ∧
      ∀ y ∈ K ∩ C, M < b y := by
  classical
  induction n generalizing K ε with
  | zero =>
    let J : Finset ℂ := (hK C hC hCU).toFinset
    have hJ : (J : Set ℂ) = K ∩ C := Set.Finite.coe_toFinset _
    have hJU : (J : Set ℂ) ⊆ ball (0 : ℂ) R := by rw [hJ]; exact inter_subset_right.trans hCU
    have hxJ : x ∉ J := fun hx => hxK (by have := hx; change x ∈ (J : Set ℂ) at this; rw [hJ] at this; exact this.1)
    obtain ⟨b, hbc, hbΔ, hbn, hbx, hbJ⟩ := exists_capped_barrier_of_finite hJU hxJ hM hε
    exact ⟨b, hbc, hbΔ, hbn, hbx, fun y hy => hbJ y (by change y ∈ (J : Set ℂ); rw [hJ]; exact hy)⟩
  | succ n ih =>
    obtain ⟨L, hLc, hL, hK⟩ := hK
    have hL' : LocallyFiniteRank (ball (0 : ℂ) R) n (L ∩ K) := hL.mono inter_subset_left
    have hxL' : x ∉ L ∩ K := fun hx => hxK hx.2
    obtain ⟨b₁, hb₁c, hb₁Δ, hb₁n, hb₁x, hb₁cover⟩ :=
      ih (hLc.inter hKc) hL' hxL' (half_pos hε)
    let W : Set ℂ := ball (0 : ℂ) R ∩ b₁ ⁻¹' Ioi M
    have hWo : IsOpen W := (hb₁c.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_Ioi
    have hLW : (L ∩ K) ∩ C ⊆ W := by
      intro y hy
      exact ⟨hCU hy.2, hb₁cover y hy⟩
    have hK' := locally_finite_off_inter_closed_deletion hKc hK
    let J : Finset ℂ := (finite_inter_compact_sdiff_neighborhood_of_locally_finite_accumulation
      hC hCU hWo hLW hK').toFinset
    have hJ : (J : Set ℂ) = K ∩ (C \ W) := Set.Finite.coe_toFinset _
    have hJU : (J : Set ℂ) ⊆ ball (0 : ℂ) R := by rw [hJ]; exact inter_subset_right.trans (sdiff_subset.trans hCU)
    have hxJ : x ∉ J := fun hx => hxK (by have := hx; change x ∈ (J : Set ℂ) at this; rw [hJ] at this; exact this.1)
    obtain ⟨b₂, hb₂c, hb₂Δ, hb₂n, hb₂x, hb₂cover⟩ :=
      exists_capped_barrier_of_finite hJU hxJ hM (half_pos hε)
    refine ⟨fun y => b₁ y + b₂ y, hb₁c.add hb₂c, hb₁Δ.add_of_nonpos hb₂Δ,
      fun y => add_nonneg (hb₁n y) (hb₂n y), by linarith, ?_⟩
    intro y hy
    by_cases hyW : y ∈ W
    · have hy1 : M < b₁ y := hyW.2
      linarith [hb₂n y]
    · have hyJ : y ∈ J := by
        change y ∈ (J : Set ℂ)
        rw [hJ]
        exact ⟨hy.1, hy.2, hyW⟩
      linarith [hb₂cover y hyJ, hb₁n y]

#print axioms LocallyFiniteRank.mono
#print axioms exists_capped_barrier_of_finite
#print axioms exists_capped_barrier_of_locallyFiniteRank

end HarmonicBalls
