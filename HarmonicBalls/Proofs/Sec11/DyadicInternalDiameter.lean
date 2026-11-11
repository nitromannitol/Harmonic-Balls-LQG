import HarmonicBalls.Proofs.Sec11.DyadicSquareOpenContainment
import HarmonicBalls.Proofs.Sec11.InternalDiameterLaw

/-! # Internal diameters of dyadic grid squares -/

namespace HarmonicBalls
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The open square concentric with a grid square, of side `7r/4`. -/
def complexOpenEnlargedGridSquare {N : ℕ} (a : ℂ) (r : ℝ)
    (i : Fin N × Fin N) : Set ℂ :=
  {z | ((i.1.val : ℝ) - 3 / 8) * r < z.re - a.re ∧
    z.re - a.re < ((i.1.val : ℝ) + 11 / 8) * r ∧
    ((i.2.val : ℝ) - 3 / 8) * r < z.im - a.im ∧
    z.im - a.im < ((i.2.val : ℝ) + 11 / 8) * r}

theorem isOpen_complexOpenEnlargedGridSquare {N : ℕ} (a : ℂ) (r : ℝ)
    (i : Fin N × Fin N) : IsOpen (complexOpenEnlargedGridSquare a r i) := by
  unfold complexOpenEnlargedGridSquare
  have hre : Continuous (fun z : ℂ => z.re - a.re) := by fun_prop
  have him : Continuous (fun z : ℂ => z.im - a.im) := by fun_prop
  exact (isOpen_lt continuous_const hre).inter
    ((isOpen_lt hre continuous_const).inter
      ((isOpen_lt continuous_const him).inter (isOpen_lt him continuous_const)))

theorem complexGridSquare_subset_open_enlarged {N : ℕ} (a : ℂ) (r : ℝ)
    (hr : 0 < r) (i : Fin N × Fin N) :
    complexGridSquare a r i ⊆ complexOpenEnlargedGridSquare a r i := by
  intro z hz
  change (i.1.val : ℝ) * r ≤ z.re - a.re ∧
    z.re - a.re ≤ ((i.1.val : ℝ) + 1) * r ∧
    (i.2.val : ℝ) * r ≤ z.im - a.im ∧
    z.im - a.im ≤ ((i.2.val : ℝ) + 1) * r at hz
  rcases hz with ⟨h1, h2, h3, h4⟩
  change ((i.1.val : ℝ) - 3 / 8) * r < z.re - a.re ∧
    z.re - a.re < ((i.1.val : ℝ) + 11 / 8) * r ∧
    ((i.2.val : ℝ) - 3 / 8) * r < z.im - a.im ∧
    z.im - a.im < ((i.2.val : ℝ) + 11 / 8) * r
  constructor <;> [nlinarith; constructor <;> [nlinarith; constructor <;> nlinarith]]

theorem complexOpenEnlargedGridSquare_subset {N : ℕ} (a : ℂ) (r : ℝ)
    (i : Fin N × Fin N) : complexOpenEnlargedGridSquare a r i ⊆
      complexEnlargedGridSquare a r i := by
  intro z hz
  exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩

/-- The internal metric diameter of a grid square measured within its open
concentric enlargement. -/
noncomputable def dyadicSquareInternalDiameter {Ω : Type*}
    (D : Ω → ℂ → ℂ → ℝ) (a : ℂ) (L : ℝ) (n : ℕ)
    (i : Fin (2 ^ n) × Fin (2 ^ n)) (ω : Ω) : ℝ≥0∞ :=
  ⨆ x ∈ complexGridSquare a (L / (2 : ℝ) ^ n) i,
    ⨆ y ∈ complexGridSquare a (L / (2 : ℝ) ^ n) i,
      internalMetric (D ω) (complexOpenEnlargedGridSquare a (L / (2 : ℝ) ^ n) i) x y

/-- Each dyadic internal diameter has an almost everywhere measurable version
under the whole-plane GFF and an LQG metric functional. -/
theorem IsWholePlaneGFF.aemeasurable_dyadicSquareInternalDiameter
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (a : ℂ) (L : ℝ) (hL : 0 < L) (n : ℕ)
    (i : Fin (2 ^ n) × Fin (2 ^ n)) :
    AEMeasurable (dyadicSquareInternalDiameter (fun ω => 𝔇 (hC ω)) a L n i) P := by
  have hr : 0 < L / (2 : ℝ) ^ n := by positivity
  exact (h.identDistrib_baseMetric_internalDiameter h 𝔇 h𝔇
    (isOpen_complexOpenEnlargedGridSquare a _ i)
    (complexGridSquare_subset_open_enlarged a _ hr i)).aemeasurable_fst

/-- A bound on the tile diameter bounds every internal distance in the tile. -/
theorem internalMetric_le_dyadicSquareInternalDiameter {Ω : Type*}
    (D : Ω → ℂ → ℂ → ℝ) (a : ℂ) (L : ℝ) (n : ℕ)
    (i : Fin (2 ^ n) × Fin (2 ^ n)) (ω : Ω) {x y : ℂ}
    (hx : x ∈ complexGridSquare a (L / (2 : ℝ) ^ n) i)
    (hy : y ∈ complexGridSquare a (L / (2 : ℝ) ^ n) i) :
    internalMetric (D ω) (complexOpenEnlargedGridSquare a (L / (2 : ℝ) ^ n) i) x y ≤
      dyadicSquareInternalDiameter D a L n i ω :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

end HarmonicBalls
