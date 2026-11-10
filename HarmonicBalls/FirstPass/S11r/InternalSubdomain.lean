import HarmonicBalls.FirstPass.S11r.CurveLengthPieces
import HarmonicBalls.Steps.Sec11.InternalMetricPaths

/-!
# The subdomain identity for iterated internal metrics, hII (fp-S11r part (b) P2, owner n2)

For a Euclidean length metric `I` on `ℂ`, an open set `D` on which the internal metric is finite on `D × D` (`hfin`),
and `V ⊆ D`, the internal metric on `V` of the real function `(u, v) ↦ (internalMetric I D u v).toReal` equals the
internal metric of `I` on `V`:

`internalMetric (fun u v => (internalMetric I D u v).toReal) V x y = internalMetric I V x y`.

This is `hII` of CHATGPT-n2-hII.md, section 1.3 (the shorter proof, using `hfin`); the statement is TRUE by the
operator's ruling of 01:57 UTC. Proof: both sides are infima over paths in `V`. For a path `P` in `V`, the `D`-internal
distances between consecutive points of a partition of `P` are bounded by the `I`-lengths of the corresponding
sub-curves (`internalMetric_le_curveLength_of_subset`), and these sum to at most the `I`-length of `P`
(superadditivity, `curveLength_add_le_general`). Conversely the `I`-length is at most the length of the
`D`-internal metric, since `I ≤ internalMetric I D` pointwise on `D`.

The axioms used: `IsEuclideanLengthMetric.internalMetric_symm`, `ofReal_eq_internalMetric`, and `internalMetric_anti`.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- A point of a path lying in `V` on `[0, 1]` (the extension by constants is in `V` as well, on `[0, 1]`). -/
theorem subdomain_extend_mem {x y : ℂ} (P : Path x y) {V : Set ℂ} (hP : ∀ t, P t ∈ V) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) : P.extend τ ∈ V := by
  have h := Path.extend_extends' P ⟨τ, hτ⟩
  rw [show P.extend τ = P ⟨τ, hτ⟩ from h]
  exact hP _

/-- Partition sums of the `D`-internal metric along a curve in `D` are bounded by the `I`-length of the curve. -/
theorem subdomain_sum_le_curveLength {I : ℂ → ℂ → ℝ} (hI : IsEuclideanLengthMetric I)
    {D : Set ℂ} {γ : ℝ → ℂ} (hγ : Continuous γ) (hγD : ∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ D) :
    ∀ (n : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ Icc (0 : ℝ) 1) →
      ∑ i ∈ Finset.range n, internalMetric I D (γ (u (i + 1))) (γ (u i)) ≤ curveLength I γ (u 0) (u n) := by
  intro n
  induction n with
  | zero => intro u _ _; simp
  | succ n ih =>
    intro u hu hu01
    rw [Finset.sum_range_succ]
    have h1 := ih u hu hu01
    have hstep : u n ≤ u (n + 1) := hu (Nat.le_succ n)
    have h0n : u 0 ≤ u n := hu (Nat.zero_le n)
    have hpiece : internalMetric I D (γ (u (n + 1))) (γ (u n)) ≤ curveLength I γ (u n) (u (n + 1)) := by
      rw [hI.internalMetric_symm D]
      refine internalMetric_le_curveLength_of_subset I hγ hstep fun τ hτ => hγD τ ⟨?_, ?_⟩
      · exact le_trans (hu01 n).1 hτ.1
      · exact le_trans hτ.2 (hu01 (n + 1)).2
    calc ∑ i ∈ Finset.range n, internalMetric I D (γ (u (i + 1))) (γ (u i))
          + internalMetric I D (γ (u (n + 1))) (γ (u n))
        ≤ curveLength I γ (u 0) (u n) + curveLength I γ (u n) (u (n + 1)) := add_le_add h1 hpiece
      _ ≤ curveLength I γ (u 0) (u (n + 1)) := curveLength_add_le_general I γ h0n hstep

/-- Comparison of the lengths of one curve for two pointwise comparable metrics on `U`. -/
theorem subdomain_curveLength_mono {D E : ℂ → ℂ → ℝ} {U : Set ℂ} {γ : ℝ → ℂ}
    (h : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (D x y) ≤ ENNReal.ofReal (E x y))
    (hγ : ∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ U) :
    curveLength D γ 0 1 ≤ curveLength E γ 0 1 := by
  unfold curveLength
  refine iSup_mono fun q => Finset.sum_le_sum fun i _ => ?_
  exact h _ (hγ _ (q.2.2.2 (i + 1))) _ (hγ _ (q.2.2.2 i))

/-- The `D`-internal length of a path in `V` is at most its `I`-length, for `V ⊆ D`. -/
theorem subdomain_pathLength_toReal_le {I : ℂ → ℂ → ℝ} (hI : IsEuclideanLengthMetric I)
    {D V : Set ℂ} (hVD : V ⊆ D) (hfin : ∀ u ∈ D, ∀ v ∈ D, internalMetric I D u v ≠ ⊤)
    {x y : ℂ} (P : Path x y) (hP : ∀ t, P t ∈ V) :
    pathLength (fun u v => (internalMetric I D u v).toReal) P ≤ pathLength I P := by
  have hγD : ∀ τ ∈ Icc (0 : ℝ) 1, P.extend τ ∈ D := fun τ hτ => hVD (subdomain_extend_mem P hP hτ)
  unfold pathLength curveLength
  refine iSup_le fun q => ?_
  have hsum : ∑ i ∈ Finset.range q.1,
        ENNReal.ofReal ((internalMetric I D (P.extend (q.2.1 (i + 1))) (P.extend (q.2.1 i))).toReal)
      = ∑ i ∈ Finset.range q.1, internalMetric I D (P.extend (q.2.1 (i + 1))) (P.extend (q.2.1 i)) :=
    Finset.sum_congr rfl fun i _ =>
      ENNReal.ofReal_toReal (hfin _ (hγD _ (q.2.2.2 (i + 1))) _ (hγD _ (q.2.2.2 i)))
  calc ∑ i ∈ Finset.range q.1,
        ENNReal.ofReal ((internalMetric I D (P.extend (q.2.1 (i + 1))) (P.extend (q.2.1 i))).toReal)
      = ∑ i ∈ Finset.range q.1, internalMetric I D (P.extend (q.2.1 (i + 1))) (P.extend (q.2.1 i)) := hsum
    _ ≤ curveLength I P.extend (q.2.1 0) (q.2.1 q.1) :=
        subdomain_sum_le_curveLength hI P.continuous_extend hγD q.1 q.2.1 q.2.2.1 q.2.2.2
    _ ≤ curveLength I P.extend 0 1 :=
        curveLength_mono_Icc I P.extend (q.2.2.2 0).1 (q.2.2.2 q.1).2

/-- The `I`-length of a path in `V` is at most its `D`-internal length, for `V ⊆ D`. -/
theorem subdomain_pathLength_le_toReal {I : ℂ → ℂ → ℝ} (hI : IsEuclideanLengthMetric I)
    {D V : Set ℂ} (hVD : V ⊆ D) (hfin : ∀ u ∈ D, ∀ v ∈ D, internalMetric I D u v ≠ ⊤)
    {x y : ℂ} (P : Path x y) (hP : ∀ t, P t ∈ V) :
    pathLength I P ≤ pathLength (fun u v => (internalMetric I D u v).toReal) P := by
  have hγD : ∀ τ ∈ Icc (0 : ℝ) 1, P.extend τ ∈ D := fun τ hτ => hVD (subdomain_extend_mem P hP hτ)
  unfold pathLength
  refine subdomain_curveLength_mono (fun a ha b hb => ?_) hγD
  show ENNReal.ofReal (I a b) ≤ ENNReal.ofReal ((internalMetric I D a b).toReal)
  rw [ENNReal.ofReal_toReal (hfin a ha b hb)]
  calc ENNReal.ofReal (I a b) = internalMetric I univ a b := hI.ofReal_eq_internalMetric a b
    _ ≤ internalMetric I D a b := internalMetric_anti I (subset_univ D) a b

/-- **hII (the subdomain identity).** For a Euclidean length metric `I`, `V ⊆ D` and `internalMetric I D` finite on
`D × D`, the internal metric on `V` of `(u, v) ↦ (internalMetric I D u v).toReal` equals `internalMetric I V`. -/
theorem internalMetric_internalMetric_toReal_of_finite {I : ℂ → ℂ → ℝ} (hI : IsEuclideanLengthMetric I)
    {D V : Set ℂ} (hVD : V ⊆ D) (hfin : ∀ u ∈ D, ∀ v ∈ D, internalMetric I D u v ≠ ⊤) (x y : ℂ) :
    internalMetric (fun u v => (internalMetric I D u v).toReal) V x y = internalMetric I V x y := by
  apply le_antisymm
  · unfold internalMetric
    exact le_iInf₂ fun P hP => le_trans (iInf₂_le P hP) (subdomain_pathLength_toReal_le hI hVD hfin P hP)
  · unfold internalMetric
    exact le_iInf₂ fun P hP => le_trans (iInf₂_le P hP) (subdomain_pathLength_le_toReal hI hVD hfin P hP)

#print axioms HarmonicBalls.internalMetric_internalMetric_toReal_of_finite

end HarmonicBalls
