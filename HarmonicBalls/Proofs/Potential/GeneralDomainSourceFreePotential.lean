import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole

/-! # Source-free Green potentials

The potential-theoretic infrastructure used here is due to Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- A compactly concentrated finite source has an integrable Green kernel at
any point of the domain outside its source set. -/
theorem integrable_greenFunction_of_compact_source
    {V K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V) (hν : ν Kᶜ = 0)
    {x : ℂ} (hx : x ∈ V \ K) : Integrable (greenFunction V x) ν :=
  greenFunctionIntegrableAwayFromPoleStep_holds V K x ν hV hx.1 hK hKV hx.2
    inferInstance hν

/-- If an open set has zero source mass, the source is concentrated on the
compact part of its original support outside that set. -/
theorem integrable_greenFunction_of_source_free_open
    {V K U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V) (hν : ν Kᶜ = 0)
    (hU : IsOpen U) (hUV : U ⊆ V) (hνU : ν U = 0) {x : ℂ} (hx : x ∈ U) :
    Integrable (greenFunction V x) ν := by
  have hKU : IsCompact (K \ U) := hK.inter_right hU.isClosed_compl
  have hcon : ν (K \ U)ᶜ = 0 := by
    apply measure_mono_null (show (K \ U)ᶜ ⊆ Kᶜ ∪ U from by
      intro y hy
      by_cases hyK : y ∈ K
      · right
        by_contra hyU
        exact hy ⟨hyK, hyU⟩
      · exact Or.inl hyK)
    exact measure_union_null hν hνU
  exact integrable_greenFunction_of_compact_source hV hKU (sdiff_subset.trans hKV) hcon
    ⟨hUV hx, fun h => h.2 hx⟩


end HarmonicBalls
