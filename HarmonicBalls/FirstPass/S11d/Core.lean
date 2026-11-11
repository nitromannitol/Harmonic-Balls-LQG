import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity

/-!
# Proposition 11.9, deterministic core of the triangle step

The repaired final step of the proof of `prop:mass-diam-gen` (corrected paper, lines 3110-3137).
 For a Euclidean length metric `D` (Fact 2.2 I), an open connected
`V`, a closed `S ⊆ V`, an open `O` with `closure (V \ S) ⊆ O`, and `S ⊆ W`, `O ⊆ W`: a bound `ε/2` on
`D(·,·; S)` over `S` and on `D(·,·; O)` over `V \ S` gives the bound `ε` on `D(·,·; W)` over `V`.

The continuity of `D(·,·; O)` on `O × O` is the deterministic lemma `IsEuclideanLengthMetric.continuousOn_internalMetric_pair`
(Steps/Sec11/InternalMetricContinuity.lean); the triangle inequality for internal metrics is
`IsEuclideanLengthMetric.internalMetric_triangle` (Steps/Sec11/InternalMetricPaths.lean).
-/

namespace HarmonicBalls

open Set Filter Topology
open scoped ENNReal

/-- Topology step (fix note (c)): if `V` is open and connected, `S ⊆ V` is closed and nonempty, and `V \ S` is
nonempty, then `closure (V \ S)` meets `S`. -/
theorem closure_diff_inter_nonempty {V S : Set ℂ} (hV : IsOpen V) (hVc : IsConnected V) (hS : IsClosed S)
    (hSV : S ⊆ V) (hSne : S.Nonempty) (hne : (V \ S).Nonempty) :
    (closure (V \ S) ∩ S).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hu : IsOpen (V \ S) := hV.sdiff hS
  have hv : IsOpen (closure (V \ S))ᶜ := isClosed_closure.isOpen_compl
  have hcover : V ⊆ (V \ S) ∪ (closure (V \ S))ᶜ := by
    intro x hx
    by_cases hxS : x ∈ S
    · right
      intro hxc
      have : x ∈ closure (V \ S) ∩ S := ⟨hxc, hxS⟩
      rw [hcon] at this
      exact this
    · exact Or.inl ⟨hx, hxS⟩
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, hb⟩ := hSne
  have hA : (V ∩ (V \ S)).Nonempty := ⟨a, ha.1, ha⟩
  have hB : (V ∩ (closure (V \ S))ᶜ).Nonempty := by
    refine ⟨b, hSV hb, ?_⟩
    intro hbc
    have : b ∈ closure (V \ S) ∩ S := ⟨hbc, hb⟩
    rw [hcon] at this
    exact this
  obtain ⟨x, hxV, hx1, hx2⟩ := hVc.2 (V \ S) (closure (V \ S))ᶜ hu hv hcover hA hB
  exact hx2 (subset_closure hx1)

/-- Continuity extension (fix note (b)): a bound on `D(·,·; O)` over `A` with `A ⊆ O` transfers to `closure A`,
because `D(·,·; O)` is continuous on `O × O` (`continuousOn_internalMetric_pair`). -/
theorem internalMetric_le_on_closure {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {O A : Set ℂ} (hO : IsOpen O) (hclO : closure A ⊆ O) {c : ℝ≥0∞}
    (h : ∀ u ∈ A, ∀ v ∈ A, internalMetric D O u v ≤ c) :
    ∀ u ∈ closure A, ∀ v ∈ closure A, internalMetric D O u v ≤ c := by
  have hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric D O p.1 p.2) (closure A ×ˢ closure A) :=
    (hD.continuousOn_internalMetric_pair hnonneg hO).mono (prod_mono hclO hclO)
  have hclosed : IsClosed ((closure A ×ˢ closure A) ∩
      (fun p : ℂ × ℂ => internalMetric D O p.1 p.2) ⁻¹' Iic c) :=
    hcont.preimage_isClosed_of_isClosed (isClosed_closure.prod isClosed_closure) isClosed_Iic
  have hsub : A ×ˢ A ⊆ (closure A ×ˢ closure A) ∩
      (fun p : ℂ × ℂ => internalMetric D O p.1 p.2) ⁻¹' Iic c := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ⟨⟨subset_closure hu, subset_closure hv⟩, h u hu v hv⟩
  have hcl := hclosed.closure_subset_iff.mpr hsub
  rw [closure_prod_eq] at hcl
  intro u hu v hv
  exact (hcl (show (u, v) ∈ closure A ×ˢ closure A from ⟨hu, hv⟩)).2

/-- The deterministic triangle step of Proposition 11.9 (fix note (d)). -/
theorem internalMetric_le_of_split {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {V S O W : Set ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (hV : IsOpen V) (hVc : IsConnected V) (hS : IsClosed S) (hSV : S ⊆ V) (hSne : S.Nonempty)
    (hO : IsOpen O) (hclO : closure (V \ S) ⊆ O) (hSW : S ⊆ W) (hOW : O ⊆ W)
    (hS_bd : ∀ u ∈ S, ∀ v ∈ S, internalMetric D S u v ≤ ENNReal.ofReal (ε / 2))
    (hO_bd : ∀ u ∈ V \ S, ∀ v ∈ V \ S, internalMetric D O u v ≤ ENNReal.ofReal (ε / 2)) :
    ∀ u ∈ V, ∀ v ∈ V, internalMetric D W u v ≤ ENNReal.ofReal ε := by
  have hsum : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  have hext := internalMetric_le_on_closure hD hnonneg hO hclO hO_bd
  intro u hu v hv
  by_cases hus : u ∈ S
  · by_cases hvs : v ∈ S
    · -- both points in `S`
      exact (internalMetric_anti D hSW u v).trans
        ((hS_bd u hus v hvs).trans (ENNReal.ofReal_le_ofReal (by linarith)))
    · -- `u ∈ S`, `v ∈ V \ S`: go through `w ∈ S ∩ closure (V \ S)`
      obtain ⟨w, hwcl, hwS⟩ := closure_diff_inter_nonempty hV hVc hS hSV hSne ⟨v, hv, hvs⟩
      have hvcl : v ∈ closure (V \ S) := subset_closure ⟨hv, hvs⟩
      calc internalMetric D W u v
          ≤ internalMetric D W u w + internalMetric D W w v := hD.internalMetric_triangle W u w v
        _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add ((internalMetric_anti D hSW u w).trans (hS_bd u hus w hwS))
            ((internalMetric_anti D hOW w v).trans (hext w hwcl v hvcl))
        _ = ENNReal.ofReal ε := hsum
  · by_cases hvs : v ∈ S
    · -- `u ∈ V \ S`, `v ∈ S`
      obtain ⟨w, hwcl, hwS⟩ := closure_diff_inter_nonempty hV hVc hS hSV hSne ⟨u, hu, hus⟩
      have hucl : u ∈ closure (V \ S) := subset_closure ⟨hu, hus⟩
      calc internalMetric D W u v
          ≤ internalMetric D W u w + internalMetric D W w v := hD.internalMetric_triangle W u w v
        _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add ((internalMetric_anti D hOW u w).trans (hext u hucl w hwcl))
            ((internalMetric_anti D hSW w v).trans (hS_bd w hwS v hvs))
        _ = ENNReal.ofReal ε := hsum
    · -- both points in `V \ S`
      exact (internalMetric_anti D hOW u v).trans
        ((hO_bd u ⟨hu, hus⟩ v ⟨hv, hvs⟩).trans (ENNReal.ofReal_le_ofReal (by linarith)))

end HarmonicBalls
