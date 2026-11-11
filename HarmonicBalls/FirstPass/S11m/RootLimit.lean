import HarmonicBalls.FirstPass.S11m.RootCut
import HarmonicBalls.FirstPass.S11m.ChainMetric

/-!
# The circle supremum of the internal metric tends to zero (route Step 3.5)

Route Step 3.5 uses the limit
`s → 0` of `sup_{y ∈ ∂B_s} D(0, y; O)`, which `RootCut.lean` (`internalMetric_root_le_sup_add_iInf`) leaves open.
Here it follows from continuity of `(z, w) ↦ D(z, w; O)` on `O × O` (a deterministic hypothesis; its almost sure form is the
frozen input `LQGInternalMetricContinuousAlphaGFFFrozen`, FirstPass/Frozen/S11g.lean:96, used in the final assembly),
with `D(0, 0; O) = 0`.
-/

namespace HarmonicBalls.S11m

open Set Metric Topology Filter

/-- If the internal metric of `D` on an open `O ∋ 0` is continuous on `O × O`, the circle suprema
`sup_{y ∈ ∂B_s} D(0, y; O)` tend to `0` as `s → 0⁺` (route Step 3.5). -/
theorem tendsto_sphere_sup_internalMetric_zero {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {O : Set ℂ}
    (hO : IsOpen O) (h0 : (0 : ℂ) ∈ O)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric D O p.1 p.2) (O ×ˢ O)) :
    Tendsto (fun s : ℝ => ⨆ y ∈ sphere (0 : ℂ) s, internalMetric D O 0 y) (𝓝[>] 0) (𝓝 0) := by
  have hg : ContinuousOn (fun y : ℂ => internalMetric D O 0 y) O := by
    have hmaps : MapsTo (fun y : ℂ => ((0 : ℂ), y)) O (O ×ˢ O) := fun y hy => ⟨h0, hy⟩
    exact hcont.comp (continuousOn_const.prodMk continuousOn_id) hmaps
  have hg0 : internalMetric D O 0 0 = 0 :=
    hD.internalMetric_self_of_mem_open (isEuclideanLengthMetric_nonneg hD) hO h0
  have ht : Tendsto (fun y : ℂ => internalMetric D O 0 y) (𝓝[O] 0) (𝓝 (internalMetric D O 0 0)) :=
    hg 0 h0
  rw [hg0] at ht
  obtain ⟨ρ, hρ, hballO⟩ := Metric.isOpen_iff.mp hO 0 h0
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hev : ∀ᶠ y in 𝓝[O] (0 : ℂ), internalMetric D O 0 y < ε := ht.eventually (gt_mem_nhds hε)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr, hr'⟩ := hev
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < min r ρ :=
    nhdsWithin_le_nhds (eventually_lt_nhds (lt_min hr hρ))
  filter_upwards [hsmall] with s hs
  refine iSup₂_le fun y hy => ?_
  have hyn : ‖y‖ = s := mem_sphere_zero_iff_norm.mp hy
  have hyO : y ∈ O := hballO (by
    rw [mem_ball_zero_iff, hyn]
    exact lt_of_lt_of_le hs (min_le_right _ _))
  exact (hr' (by
    rw [dist_zero_right, hyn]
    exact lt_of_lt_of_le hs (min_le_left _ _)) hyO).le

/-- Root recovery (route Step 3.5): for `x ≠ 0` with `D(0, x; O) < ∞`, the infima `inf_{y ∈ ∂B_s} D(y, x; O \ {0})`
tend to `D(0, x; O)` as `s → 0⁺`. The finiteness hypothesis is the route's standing assumption for connected `O`; its
source is not yet located (see the report). -/
theorem tendsto_sphere_iInf_internalMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {O : Set ℂ}
    (hO : IsOpen O) (h0 : (0 : ℂ) ∈ O) {x : ℂ} (hx0 : x ≠ 0) (hfin : internalMetric D O 0 x ≠ ⊤)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric D O p.1 p.2) (O ×ˢ O)) :
    Tendsto (fun s : ℝ => ⨅ y ∈ sphere (0 : ℂ) s, internalMetric D (O \ {0}) y x) (𝓝[>] 0)
      (𝓝 (internalMetric D O 0 x)) := by
  have hsup := tendsto_sphere_sup_internalMetric_zero hD hO h0 hcont
  rw [ENNReal.tendsto_nhds hfin]
  intro ε hε
  have hsupε : ∀ᶠ s in 𝓝[>] (0 : ℝ), (⨆ y ∈ sphere (0 : ℂ) s, internalMetric D O 0 y) < ε :=
    hsup.eventually (gt_mem_nhds hε)
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := eventually_mem_nhdsWithin
  have hlt : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < ‖x‖ :=
    nhdsWithin_le_nhds (eventually_lt_nhds (norm_pos_iff.mpr hx0))
  have hnorm : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s < ‖x‖ := hpos.and hlt
  filter_upwards [hsupε, hnorm] with s hs hsn
  constructor
  · have hroot := internalMetric_root_le_sup_add_iInf D hD O s x
    have hinf : (⨅ y ∈ sphere (0 : ℂ) s, internalMetric D (O \ {0}) y x) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (iInf_sphere_internalMetric_le D hsn.1 hsn.2)
    refine tsub_le_iff_right.mpr (le_of_lt ?_)
    calc internalMetric D O 0 x
        ≤ (⨆ y ∈ sphere (0 : ℂ) s, internalMetric D O 0 y) + ⨅ y ∈ sphere (0 : ℂ) s,
            internalMetric D (O \ {0}) y x := hroot
      _ < ε + ⨅ y ∈ sphere (0 : ℂ) s, internalMetric D (O \ {0}) y x :=
          ENNReal.add_lt_add_right hinf hs
      _ = (⨅ y ∈ sphere (0 : ℂ) s, internalMetric D (O \ {0}) y x) + ε := add_comm _ _
  · exact (iInf_sphere_internalMetric_le D hsn.1 hsn.2).trans le_self_add

end HarmonicBalls.S11m

