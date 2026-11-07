import HarmonicBalls.Proposed.Birkhoff

/-!
# Birkhoff averages of a stationary sequence

The shift on the sequence space turns stationarity into a measure-preserving
map, to which the pointwise ergodic theorem applies. This is the convergence
step in Lemma 8.3, before using triviality of the GFF germ.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology

/-- The left shift on real sequences is measurable. -/
theorem measurable_sequence_shift : Measurable (fun x : ℕ → ℝ => fun n => x (n + 1)) := by
  exact Measurable.of_eval fun n => measurable_pi_apply (n + 1)

/-- Birkhoff's pointwise theorem for a stationary real sequence. Stationarity
is equality in law of the whole sequence and its left shift. -/
theorem ae_tendsto_stationary_average {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hInt : Integrable (X 0) P)
    (hstat : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω)) :
    ∀ᵐ ω ∂P, ∃ L : ℝ,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, X n ω) atTop (𝓝 L) := by
  let path : Ω → ℕ → ℝ := fun ω n => X n ω
  let shift : (ℕ → ℝ) → (ℕ → ℝ) := fun x n => x (n + 1)
  let Q : Measure (ℕ → ℝ) := P.map path
  have hpath : Measurable path := Measurable.of_eval hX
  have hshift : Measurable shift := measurable_sequence_shift
  have hpres : MeasurePreserving shift Q Q := by
    refine ⟨hshift, ?_⟩
    change (P.map path).map shift = P.map path
    rw [Measure.map_map hshift hpath]
    exact hstat
  have heval : Measurable (fun x : ℕ → ℝ => x 0) := measurable_pi_apply 0
  have h0 : Integrable (fun x : ℕ → ℝ => x 0) Q := by
    apply (integrable_map_measure heval.aestronglyMeasurable hpath.aemeasurable).2
    exact hInt
  have hae := pointwiseBirkhoff_of_latticeProb Q shift (fun x => x 0) hpres heval h0
  have hae' : ∀ᵐ ω ∂P, ∃ L : ℝ,
      Tendsto (fun N : ℕ => birkhoffSum shift (fun x => x 0) N (path ω) / N) atTop (𝓝 L) :=
    ae_of_ae_map hpath.aemeasurable hae
  filter_upwards [hae'] with ω ⟨L, hL⟩
  refine ⟨L, ?_⟩
  convert hL using 1
  funext N
  unfold birkhoffSum
  simp only [div_eq_mul_inv, mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hiter : ∀ k : ℕ, ∀ x : ℕ → ℝ, ∀ m : ℕ, (shift^[k] x) m = x (m + k) := by
    intro k
    induction k with
    | zero => intro x m; simp
    | succ k ih =>
      intro x m
      rw [Function.iterate_succ_apply']
      change (shift^[k] x) (m + 1) = x (m + (k + 1))
      rw [ih]
      congr 1; omega
  simpa [path] using (hiter n (path ω) 0).symm

end HarmonicBalls
