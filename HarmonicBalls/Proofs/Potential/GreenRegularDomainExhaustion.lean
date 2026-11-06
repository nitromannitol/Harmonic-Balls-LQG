import HarmonicBalls.Proofs.Sec6.RelativelyCompactExhaustion

/-! # Relatively compact open exhaustions with a fixed pole

This is the topological part of a Green-regular exhaustion. The boundary
regularity of the resulting domains is a separate question.
-/

namespace HarmonicBalls

open Set Metric Filter
open scoped Topology

/-- An open subset of the plane admits an increasing relatively compact open
exhaustion containing any prescribed point at every stage. -/
theorem exists_open_relativelyCompact_exhaustion {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) :
    ∃ V : ℕ → Set ℂ, (∀ n, IsOpen (V n)) ∧ Monotone V ∧
      (⋃ n, V n) = U ∧ (∀ n, closure (V n) ⊆ U) ∧ ∀ n, z ∈ V n := by
  obtain ⟨D, hopen, hmono, -, hnext, hunion⟩ :=
    Section6.exists_relativelyCompact_open_exhaustion hU
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hunion.symm ▸ hz)
  let V (n : ℕ) := D (k + n)
  refine ⟨V, fun n => hopen _, ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    exact hmono (by omega)
  · apply Subset.antisymm
    · rw [← hunion]
      exact iUnion_subset fun n => subset_iUnion D _
    · rw [← hunion]
      refine iUnion_subset fun n => ?_
      exact (hmono (show n ≤ k + n by omega)).trans (subset_iUnion V n)
  · intro n
    rw [← hunion]
    exact (hnext _).trans (subset_iUnion D _)
  · intro n
    exact hmono (show k ≤ k + n by omega) hk

/-- Every open planar set has a nested exhaustion by finite unions of discs
whose closures lie in the set, and the union at every stage contains the
chosen pole. No boundary regularity of the unions is asserted. -/
theorem exists_finite_disc_open_exhaustion {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) :
    ∃ (r : U → ℝ) (F : ℕ → Finset U),
      (∀ x, 0 < r x ∧ closedBall (x : ℂ) (r x) ⊆ U) ∧
      Monotone F ∧
      let V : ℕ → Set ℂ := fun n => ⋃ x ∈ F n, ball (x : ℂ) (r x)
      (∀ n, IsOpen (V n)) ∧ Monotone V ∧ (⋃ n, V n) = U ∧
        (∀ n, closure (V n) ⊆ U) ∧ ∀ n, z ∈ V n := by
  classical
  obtain ⟨D, hDo, hDm, hDc, hDn, hDU⟩ :=
    Section6.exists_relativelyCompact_open_exhaustion hU
  have hDU' (n : ℕ) : closure (D n) ⊆ U := by
    rw [← hDU]
    exact (hDn n).trans (subset_iUnion D _)
  have hr (x : U) : ∃ r : ℝ, 0 < r ∧ closedBall (x : ℂ) r ⊆ U := by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x x.property
    refine ⟨ε / 2, by linarith, ?_⟩
    exact (closedBall_subset_ball (by linarith)).trans hεU
  choose r hr using hr
  let B (x : U) : Set ℂ := ball (x : ℂ) (r x)
  have hcover : U ⊆ ⋃ x : U, B x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩).1⟩
  have hfinite (n : ℕ) : ∃ F : Finset U, closure (D n) ⊆ ⋃ x ∈ F, B x :=
    (hDc n).elim_finite_subcover B (fun _ => isOpen_ball) ((hDU' n).trans hcover)
  choose G hG using hfinite
  let F (n : ℕ) : Finset U := insert ⟨z, hz⟩ ((Finset.range (n + 1)).biUnion G)
  have hFmono : Monotone F := by
    intro m n hmn x hx
    simp only [F, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_range] at hx ⊢
    rcases hx with h | ⟨k, hk, hx⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, by omega, hx⟩
  let V (n : ℕ) : Set ℂ := ⋃ x ∈ F n, B x
  refine ⟨r, F, hr, hFmono, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact isOpen_iUnion fun x => isOpen_iUnion fun _ => isOpen_ball
  · intro m n hmn x hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨a, hFmono hmn ha, hxa⟩
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      obtain ⟨a, haF, hxa⟩ := mem_iUnion₂.mp hn
      exact hr a |>.2 (ball_subset_closedBall hxa)
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hDU.symm ▸ hx)
      obtain ⟨a, haG, hxa⟩ := mem_iUnion₂.mp (hG n (subset_closure hn))
      refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨?_, hxa⟩⟩⟩
      simp only [F, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_range]
      exact Or.inr ⟨n, by omega, haG⟩
  · intro n
    change closure (⋃ x ∈ F n, B x) ⊆ U
    rw [(F n).closure_biUnion]
    refine iUnion_subset fun x => iUnion_subset fun _ => ?_
    exact (closure_minimal ball_subset_closedBall isClosed_closedBall).trans (hr x).2
  · intro n
    refine mem_iUnion.mpr ⟨⟨z, hz⟩, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · simp [F]
    · exact mem_ball_self (hr ⟨z, hz⟩).1

/-- Finite-disc Green boundary limits imply the desired relatively compact
Green-regular exhaustion. The finite-disc limit is an explicit hypothesis and
is not proved by this reduction. -/
theorem exists_greenRegular_exhaustion_of_finite_disc_boundary_limits
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (hdisc : ∀ (r : U → ℝ) (F : Finset U),
      (∀ x, 0 < r x ∧ closedBall (x : ℂ) (r x) ⊆ U) →
      z ∈ ⋃ x ∈ F, ball (x : ℂ) (r x) →
      ∀ y ∈ closure (⋃ x ∈ F, ball (x : ℂ) (r x)),
        y ∉ ⋃ x ∈ F, ball (x : ℂ) (r x) →
        Tendsto (greenFunction (⋃ x ∈ F, ball (x : ℂ) (r x)) z)
          (𝓝[⋃ x ∈ F, ball (x : ℂ) (r x)] y) (𝓝 0)) :
    ∃ V : ℕ → Set ℂ, (∀ n, IsOpen (V n)) ∧ Monotone V ∧
      (⋃ n, V n) = U ∧ (∀ n, closure (V n) ⊆ U) ∧
      (∀ n, z ∈ V n) ∧ ∀ n, ∀ y ∈ closure (V n), y ∉ V n →
        Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0) := by
  obtain ⟨r, F, hr, _, hopen, hmono, hcover, hcompact, hpole⟩ :=
    exists_finite_disc_open_exhaustion hU hz
  refine ⟨fun n => ⋃ x ∈ F n, ball (x : ℂ) (r x), hopen, hmono, hcover,
    hcompact, hpole, ?_⟩
  intro n y hy hyout
  exact hdisc r (F n) hr (hpole n) y hy hyout

#print axioms exists_greenRegular_exhaustion_of_finite_disc_boundary_limits
#print axioms exists_open_relativelyCompact_exhaustion
#print axioms exists_finite_disc_open_exhaustion

end HarmonicBalls
