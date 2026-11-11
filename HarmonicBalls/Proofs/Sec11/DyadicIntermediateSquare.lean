import HarmonicBalls.Proofs.Sec11.DyadicInternalDiameter

/-! # Intermediate squares in the dyadic mass construction -/

namespace HarmonicBalls
open Set MeasureTheory
open scoped ENNReal

/-- The closed square concentric with a grid square of side `r`, with side
`3r/2`. -/
def complexIntermediateGridSquare {N : ℕ} (a : ℂ) (r : ℝ)
    (i : Fin N × Fin N) : Set ℂ :=
  {z | ((i.1.val : ℝ) - 1 / 4) * r ≤ z.re - a.re ∧
    z.re - a.re ≤ ((i.1.val : ℝ) + 5 / 4) * r ∧
    ((i.2.val : ℝ) - 1 / 4) * r ≤ z.im - a.im ∧
    z.im - a.im ≤ ((i.2.val : ℝ) + 5 / 4) * r}

/-- The open square corresponding to the intermediate square. -/
def complexOpenIntermediateGridSquare {N : ℕ} (a : ℂ) (r : ℝ)
    (i : Fin N × Fin N) : Set ℂ :=
  {z | ((i.1.val : ℝ) - 1 / 4) * r < z.re - a.re ∧
    z.re - a.re < ((i.1.val : ℝ) + 5 / 4) * r ∧
    ((i.2.val : ℝ) - 1 / 4) * r < z.im - a.im ∧
    z.im - a.im < ((i.2.val : ℝ) + 5 / 4) * r}

theorem isOpen_complexOpenIntermediateGridSquare {N : ℕ} (a : ℂ) (r : ℝ)
    (i : Fin N × Fin N) : IsOpen (complexOpenIntermediateGridSquare a r i) := by
  unfold complexOpenIntermediateGridSquare
  have hre : Continuous (fun z : ℂ => z.re - a.re) := by fun_prop
  have him : Continuous (fun z : ℂ => z.im - a.im) := by fun_prop
  exact (isOpen_lt continuous_const hre).inter ((isOpen_lt hre continuous_const).inter
    ((isOpen_lt continuous_const him).inter (isOpen_lt him continuous_const)))

theorem isClosed_complexIntermediateGridSquare {N : ℕ} (a : ℂ) (r : ℝ)
    (i : Fin N × Fin N) : IsClosed (complexIntermediateGridSquare a r i) := by
  unfold complexIntermediateGridSquare
  have hre : Continuous (fun z : ℂ => z.re - a.re) := by fun_prop
  have him : Continuous (fun z : ℂ => z.im - a.im) := by fun_prop
  exact (isClosed_le continuous_const hre).inter ((isClosed_le hre continuous_const).inter
    ((isClosed_le continuous_const him).inter (isClosed_le him continuous_const)))

/-- The mass-carrying tile lies strictly inside the intermediate square. -/
theorem complexGridSquare_subset_interior_intermediate {N : ℕ} (a : ℂ) (r : ℝ)
    (hr : 0 < r) (i : Fin N × Fin N) :
    complexGridSquare a r i ⊆ interior (complexIntermediateGridSquare a r i) := by
  have hop : complexOpenIntermediateGridSquare a r i ⊆
      interior (complexIntermediateGridSquare a r i) :=
    (isOpen_complexOpenIntermediateGridSquare a r i).subset_interior_iff.mpr (by
      intro z hz
      exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩)
  intro z hz
  apply hop
  change (i.1.val : ℝ) * r ≤ z.re - a.re ∧
    z.re - a.re ≤ ((i.1.val : ℝ) + 1) * r ∧
    (i.2.val : ℝ) * r ≤ z.im - a.im ∧
    z.im - a.im ≤ ((i.2.val : ℝ) + 1) * r at hz
  rcases hz with ⟨h1, h2, h3, h4⟩
  change ((i.1.val : ℝ) - 1 / 4) * r < z.re - a.re ∧
    z.re - a.re < ((i.1.val : ℝ) + 5 / 4) * r ∧
    ((i.2.val : ℝ) - 1 / 4) * r < z.im - a.im ∧
    z.im - a.im < ((i.2.val : ℝ) + 5 / 4) * r
  constructor <;> [nlinarith; constructor <;> [nlinarith; constructor <;> nlinarith]]

/-- The closed intermediate square is contained in the open larger square. -/
theorem complexIntermediateGridSquare_subset_open_enlarged {N : ℕ} (a : ℂ) (r : ℝ)
    (hr : 0 < r) (i : Fin N × Fin N) :
    complexIntermediateGridSquare a r i ⊆ complexOpenEnlargedGridSquare a r i := by
  intro z hz
  rcases hz with ⟨h1, h2, h3, h4⟩
  change ((i.1.val : ℝ) - 3 / 8) * r < z.re - a.re ∧
    z.re - a.re < ((i.1.val : ℝ) + 11 / 8) * r ∧
    ((i.2.val : ℝ) - 3 / 8) * r < z.im - a.im ∧
    z.im - a.im < ((i.2.val : ℝ) + 11 / 8) * r
  constructor <;> [nlinarith; constructor <;> [nlinarith; constructor <;> nlinarith]]

/-- Internal diameter of the closed intermediate square in the open larger
square, as required in the core-gluing argument. -/
noncomputable def dyadicIntermediateInternalDiameter {Ω : Type*}
    (D : Ω → ℂ → ℂ → ℝ) (a : ℂ) (L : ℝ) (n : ℕ)
    (i : Fin (2 ^ n) × Fin (2 ^ n)) (ω : Ω) : ℝ≥0∞ :=
  ⨆ x ∈ complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
    ⨆ y ∈ complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
      internalMetric (D ω) (complexOpenEnlargedGridSquare a (L / (2 : ℝ) ^ n) i) x y

theorem IsWholePlaneGFF.aemeasurable_dyadicIntermediateInternalDiameter
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (a : ℂ) (L : ℝ) (hL : 0 < L) (n : ℕ)
    (i : Fin (2 ^ n) × Fin (2 ^ n)) :
    AEMeasurable (dyadicIntermediateInternalDiameter (fun ω => 𝔇 (hC ω)) a L n i) P := by
  have hr : 0 < L / (2 : ℝ) ^ n := by positivity
  exact (h.identDistrib_baseMetric_internalDiameter h 𝔇 h𝔇
    (isOpen_complexOpenEnlargedGridSquare a _ i)
    (complexIntermediateGridSquare_subset_open_enlarged a _ hr i)).aemeasurable_fst

end HarmonicBalls
