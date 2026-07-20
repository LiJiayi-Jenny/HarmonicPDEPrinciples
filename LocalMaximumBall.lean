import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Local constancy near an interior maximum

This file formalizes the following local step in the strong maximum principle.

Let `U` be open, let `x₀ ∈ U`, and let `u` be continuous on `closure U`.
Assume that `u x₀` is the maximum of `u` on `closure U`, and assume a ball
mean-value property for `u`.  Then there is an `r > 0` such that
`closedBall x₀ r ⊆ U` and `u = u x₀` on `ball x₀ r`.

Important: `C²` regularity alone does *not* imply this conclusion.  The mean-value
property (or harmonicity together with a theorem proving the mean-value property)
is essential.  In general dimension, the mean-value property is a standard
mathematical theorem for harmonic functions; it remains an explicit provider
here only because that theorem has not yet been formalized in this project.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace StrongMaximumPrinciple

/-! ## 1. Ambient Euclidean space -/

/-- The real Euclidean space `ℝⁿ`.  Using `EuclideanSpace` supplies the norm,
distance, inner product, topology, Borel structure, and Lebesgue volume. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## 2. Domain operations already present in mathlib

For `U : Set (E n)`:

* `closure U` is `\overline U`;
* `frontier U` is `∂U`;
* `Metric.ball x r` is the open ball `B(x,r)`;
* `Metric.closedBall x r` is the closed ball `\overline{B(x,r)}`.

No new definition and no explicit use of `Filter` are needed to construct a ball.
Filters occur internally in mathlib's definitions of openness and continuity.
-/

/-- Distance from `x` to the boundary of `U`.

This is included for mathematical readability.  The local proof below uses the
simpler and more general fact that an interior point of an open set has a small
closed ball contained in the set.
-/
noncomputable def distToBoundary {n : ℕ} (x : E n) (U : Set (E n)) : ℝ :=
  Metric.infDist x (frontier U)

/-! ## 3. Maximum predicates

In Lean it is usually better not to introduce `max_{x ∈ s} u x` as a chosen
number.  `IsGreatest (u '' s) M` says simultaneously that `M` belongs to the
range of `u` on `s` and that every value there is at most `M`.
-/

/-- Formal meaning of `u x₀ = max_{x ∈ closure U} u x`.

The maximizing point `x₀` is part of the data, so its membership in `closure U`
is recorded explicitly. -/
def AttainsMaxOnClosure {n : ℕ}
    (u : E n → ℝ) (U : Set (E n)) (x₀ : E n) : Prop :=
  x₀ ∈ closure U ∧ IsMaxOn u (closure U) x₀

/-- Formal meaning of `M = max_{x ∈ frontier U} u x`.

Only the maximum value `M` is retained; no maximizing boundary point is named. -/
def IsMaximumValueOnFrontier {n : ℕ}
    (u : E n → ℝ) (U : Set (E n)) (M : ℝ) : Prop :=
  IsGreatest (u '' frontier U) M

/-! ## 4. Ball volume and ball average -/

/-- The real-valued Lebesgue volume `|B(x,r)|` of an open ball. -/
noncomputable def ballVolume {n : ℕ} (x : E n) (r : ℝ) : ℝ :=
  (volume (Metric.ball x r)).toReal

/-- The normalized average

`(1 / |B(x,r)|) * ∫ y in B(x,r), u y`.

For the main API we use the equivalent unnormalized identity in
`HasBallMeanValuePropertyOn`; this avoids division and cancellation in every
downstream proof.
-/
noncomputable def ballAverage {n : ℕ}
    (u : E n → ℝ) (x : E n) (r : ℝ) : ℝ :=
  (ballVolume x r)⁻¹ * ∫ y in Metric.ball x r, u y

/-- The interface to be supplied by the separate mean-value project.

Mathematically this says

`∫ y in B(x,r), u y = |B(x,r)| * u x`

whenever the closed ball is contained in `U`.  For a positive-radius ball this
is equivalent to `ballAverage u x r = u x`.
-/
def HasBallMeanValuePropertyOn {n : ℕ}
    (u : E n → ℝ) (U : Set (E n)) : Prop :=
  ∀ ⦃x : E n⦄, x ∈ U →
    ∀ ⦃r : ℝ⦄, 0 < r → Metric.closedBall x r ⊆ U →
      (∫ y in Metric.ball x r, u y) = ballVolume x r * u x

/-! ## 5. A small closed ball inside an open set -/

/-- If `x₀` belongs to an open set `U`, then some positive-radius closed ball
centered at `x₀` is contained in `U`.

The proof first obtains `ball x₀ ε ⊆ U`, then takes `r = ε / 2`.
-/
lemma exists_closedBall_subset_of_isOpen {n : ℕ}
    {U : Set (E n)} {x₀ : E n}
    (hU_open : IsOpen U) (hx₀ : x₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall x₀ r ⊆ U := by
  rcases Metric.mem_nhds_iff.mp (hU_open.mem_nhds hx₀) with
    ⟨ε, hε_pos, hεU⟩
  refine ⟨ε / 2, by positivity, ?_⟩
  apply (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans
  exact hεU

/-! ## 6. Core local-constancy theorem -/

/-- Core theorem.  Only the assumptions genuinely used by the local argument
appear here.

The proof has four parts:

1. choose a small closed ball inside `U`;
2. compare the integral of `u` with the integral of the constant `M = u x₀`;
3. use `integral_eq_iff_of_ae_le` to get equality almost everywhere;
4. use continuity and positivity of Lebesgue measure on nonempty open sets to
   upgrade almost-everywhere equality to pointwise equality on the ball.
-/
theorem exists_ball_eq_const_of_meanValue {n : ℕ}
    {U : Set (E n)} {u : E n → ℝ} {x₀ : E n}
    (hU_open : IsOpen U)
    (hu_cont : ContinuousOn u (closure U))
    (hx₀ : x₀ ∈ U)
    (hmax : AttainsMaxOnClosure u U x₀)
    (hmean : HasBallMeanValuePropertyOn u U) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall x₀ r ⊆ U ∧
      Set.EqOn u (fun _ : E n => u x₀) (Metric.ball x₀ r) := by
  rcases exists_closedBall_subset_of_isOpen hU_open hx₀ with
    ⟨r, hr_pos, hclosedBall_U⟩
  refine ⟨r, hr_pos, hclosedBall_U, ?_⟩

  -- Abbreviations for the ball and the maximum value.
  let B : Set (E n) := Metric.ball x₀ r
  let M : ℝ := u x₀

  have hB_open : IsOpen B := by
    simp [B]

  have hB_measurable : MeasurableSet B :=
    hB_open.measurableSet

  have hB_closedBall : B ⊆ Metric.closedBall x₀ r := by
    simpa [B] using Metric.ball_subset_closedBall

  have hB_U : B ⊆ U :=
    hB_closedBall.trans hclosedBall_U

  have hclosedBall_closure : Metric.closedBall x₀ r ⊆ closure U :=
    hclosedBall_U.trans subset_closure

  -- Continuity and integrability of `u` on the ball.
  have hu_closedBall : ContinuousOn u (Metric.closedBall x₀ r) :=
    hu_cont.mono hclosedBall_closure

  have hu_B : ContinuousOn u B :=
    hu_closedBall.mono hB_closedBall

  have hu_integrable_closedBall :
      IntegrableOn u (Metric.closedBall x₀ r) volume :=
    hu_closedBall.integrableOn_compact (μ := volume) (isCompact_closedBall x₀ r)

  have hu_integrable_B : IntegrableOn u B volume :=
    hu_integrable_closedBall.mono_set hB_closedBall

  -- The constant function `M` is continuous and integrable on the same ball.
  have hM_closedBall :
      ContinuousOn (fun _ : E n => M) (Metric.closedBall x₀ r) :=
    continuousOn_const

  have hM_integrable_closedBall :
      IntegrableOn (fun _ : E n => M) (Metric.closedBall x₀ r) volume :=
    hM_closedBall.integrableOn_compact (μ := volume) (isCompact_closedBall x₀ r)

  have hM_integrable_B : IntegrableOn (fun _ : E n => M) B volume :=
    hM_integrable_closedBall.mono_set hB_closedBall

  -- Since `M` is the maximum on `closure U`, `u y ≤ M` on the ball.
  have hu_le_M_ae :
      u ≤ᵐ[volume.restrict B] (fun _ : E n => M) := by
    filter_upwards [ae_restrict_mem hB_measurable] with y hy
    exact hmax.2 (subset_closure (hB_U hy))

  -- Mean-value identity for `u`.
  have hu_mean :
      (∫ y in B, u y) = ballVolume x₀ r * M := by
    simpa [B, M] using hmean hx₀ hr_pos hclosedBall_U

  -- The integral of the constant `M` is also `|B| * M`.
  have hM_mean :
      (∫ _y in B, M) = ballVolume x₀ r * M := by
    simp [B, ballVolume, Measure.real]

  have h_integrals_equal :
      (∫ y in B, u y) = ∫ _y in B, M :=
    hu_mean.trans hM_mean.symm

  -- Equality of integrals under the pointwise inequality yields a.e. equality.
  have hu_eq_M_ae :
      u =ᵐ[volume.restrict B] (fun _ : E n => M) :=
    (integral_eq_iff_of_ae_le hu_integrable_B hM_integrable_B hu_le_M_ae).mp
      h_integrals_equal

  -- A continuous function that agrees a.e. with a constant on an open set
  -- agrees with it everywhere there.  Lebesgue volume is positive on every
  -- nonempty open subset of Euclidean space.
  have hu_eq_M_on_B : Set.EqOn u (fun _ : E n => M) B :=
    volume.eqOn_open_of_ae_eq hu_eq_M_ae hB_open hu_B continuousOn_const

  simpa [B, M] using hu_eq_M_on_B

/-! ## 7. The requested public API -/

/-- The user's requested API, retaining all the assumptions in the mathematical
statement.  The leading underscores record that nonemptiness, connectedness,
boundedness, and `C²` regularity are not needed for this *local* step.

They will become important in later steps:

* boundedness + finite dimensionality give compactness of `closure U`;
* compactness + continuity give existence of a maximum;
* connectedness upgrades local constancy of all maximum points to global
  constancy.
-/
theorem local_constancy_api {n : ℕ}
    {U : Set (E n)} {u : E n → ℝ} {x₀ : E n}
    (_hU_nonempty : U.Nonempty)
    (_hU_preconnected : IsPreconnected U)
    (_hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (_hu_C2 : ContDiffOn ℝ 2 u U)
    (hu_cont_closure : ContinuousOn u (closure U))
    (hx₀ : x₀ ∈ U)
    (hmax : AttainsMaxOnClosure u U x₀)
    (hmean : HasBallMeanValuePropertyOn u U) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall x₀ r ⊆ U ∧
      ∀ y ∈ Metric.ball x₀ r, u y = u x₀ := by
  rcases exists_ball_eq_const_of_meanValue
      hU_open hu_cont_closure hx₀ hmax hmean with
    ⟨r, hr, hclosed, heq⟩
  exact ⟨r, hr, hclosed, fun y hy => heq hy⟩

/-! ## 8. Harmonic-function wrapper -/

/-- A cleaner wrapper using mathlib's existing structure
`InnerProductSpace.HarmonicContOnCl u U`, which packages

* harmonicity (and hence `C²` regularity) on `U`, and
* continuity on `closure U`.

The separate `hmean` parameter remains until the general `ℝⁿ` mean-value theorem
is supplied.
-/
theorem harmonic_local_constancy_api {n : ℕ}
    {U : Set (E n)} {u : E n → ℝ} {x₀ : E n}
    (hU_open : IsOpen U)
    (hu : InnerProductSpace.HarmonicContOnCl u U)
    (hx₀ : x₀ ∈ U)
    (hmax : AttainsMaxOnClosure u U x₀)
    (hmean : HasBallMeanValuePropertyOn u U) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall x₀ r ⊆ U ∧
      ∀ y ∈ Metric.ball x₀ r, u y = u x₀ := by
  rcases exists_ball_eq_const_of_meanValue
      hU_open hu.continuousOn hx₀ hmax hmean with
    ⟨r, hr, hclosed, heq⟩
  exact ⟨r, hr, hclosed, fun y hy => heq hy⟩

/-! ## 9. Conditional wrapper matching the requested mathematical input

This theorem keeps nonemptiness, preconnectedness, and boundedness in the public
signature so that it matches the textbook statement.  As above, these three
hypotheses are not used in this local step.  The temporary `hmean` argument is
the explicit provider for the general `ℝⁿ` mean-value theorem; it records a
formalization gap, not an additional mathematical restriction on harmonic
functions.  Once a theorem deriving it from `hu.harmonicOnNhd` is available,
callers will no longer need to supply it by hand.
-/
theorem requested_harmonic_local_constancy_api {n : ℕ}
    {U : Set (E n)} {u : E n → ℝ} {x₀ : E n}
    (_hU_nonempty : U.Nonempty)
    (_hU_preconnected : IsPreconnected U)
    (_hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (hu : InnerProductSpace.HarmonicContOnCl u U)
    (hx₀ : x₀ ∈ U)
    (hmax : AttainsMaxOnClosure u U x₀)
    (hmean : HasBallMeanValuePropertyOn u U) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall x₀ r ⊆ U ∧
      ∀ y ∈ Metric.ball x₀ r, u y = u x₀ := by
  exact harmonic_local_constancy_api hU_open hu hx₀ hmax hmean

end StrongMaximumPrinciple
