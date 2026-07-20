import LocalMaximumBall
import ComplexBallMeanValue
import Mathlib.Topology.Connected.Clopen

/-!
# The boundary and closure have the same maximum value

This file continues `LocalMaximumBall.lean`.

Assume that a harmonic function reaches its maximum over `closure U` at an
interior point `x₀`.  The strong maximum principle first makes the function
constant on the connected open set `U`.  Continuity on `closure U` then makes
it constant on all of `closure U`.  Since a nonempty bounded domain in a
positive-dimensional Euclidean space has nonempty frontier, the same value is
also attained on `frontier U`.

The general-dimensional theorem is conditional on
`HasBallMeanValuePropertyOn u U`, because the corresponding general `ℝⁿ`
mean-value theorem is still the external API of `LocalMaximumBall.lean`.
The final section gives an unconditional two-dimensional wrapper using
`ComplexBallMeanValue.lean`.
-/

open Set

noncomputable section

namespace StrongMaximumPrinciple

private def boundaryMaximumLevelSet {n : ℕ}
    (U : Set (E n)) (u : E n → ℝ) (M : ℝ) : Set U :=
  {x | u (x : E n) = M}

private lemma isClosed_boundaryMaximumLevelSet {n : ℕ}
    {U : Set (E n)} {u : E n → ℝ} {M : ℝ}
    (hu_cont : ContinuousOn u U) :
    IsClosed (boundaryMaximumLevelSet U u M) := by
  rw [show boundaryMaximumLevelSet U u M = (U.restrict u) ⁻¹' {M} by
    ext x
    simp [boundaryMaximumLevelSet]]
  exact isClosed_singleton.preimage hu_cont.restrict

private lemma isOpen_boundaryMaximumLevelSet_of_meanValue {n : ℕ}
    {U : Set (E n)} {u : E n → ℝ} {x₀ : E n}
    (hU_open : IsOpen U)
    (hu_cont : ContinuousOn u (closure U))
    (hmax : AttainsMaxOnClosure u U x₀)
    (hmean : HasBallMeanValuePropertyOn u U) :
    IsOpen (boundaryMaximumLevelSet U u (u x₀)) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx_eq : u (x : E n) = u x₀ := by
    simpa [boundaryMaximumLevelSet] using hx
  have hmax_x : AttainsMaxOnClosure u U (x : E n) := by
    refine ⟨subset_closure x.property, ?_⟩
    intro y hy
    rw [hx_eq]
    exact hmax.2 hy
  rcases exists_ball_eq_const_of_meanValue
      hU_open hu_cont x.property hmax_x hmean with
    ⟨r, hr_pos, _hclosedBall_U, heq⟩
  let V : Set U :=
    ((↑) : U → E n) ⁻¹' Metric.ball (x : E n) r
  have hV_open : IsOpen V := by
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  have hxV : x ∈ V := by
    simp [V, hr_pos]
  have hV_subset : V ⊆ boundaryMaximumLevelSet U u (u x₀) := by
    intro y hy
    have hy_ball : (y : E n) ∈ Metric.ball (x : E n) r := by
      change (y : E n) ∈ Metric.ball (x : E n) r at hy
      exact hy
    have hy_eq_x : u (y : E n) = u (x : E n) := heq hy_ball
    change u (y : E n) = u x₀
    exact hy_eq_x.trans hx_eq
  exact Filter.mem_of_superset (hV_open.mem_nhds hxV) hV_subset

private theorem eqOn_const_of_meanValue_of_isPreconnected_boundary {n : ℕ}
    {U : Set (E n)} {u : E n → ℝ} {x₀ : E n}
    (hU_preconnected : IsPreconnected U)
    (hU_open : IsOpen U)
    (hu_cont : ContinuousOn u (closure U))
    (hx₀ : x₀ ∈ U)
    (hmax : AttainsMaxOnClosure u U x₀)
    (hmean : HasBallMeanValuePropertyOn u U) :
    Set.EqOn u (fun _ : E n => u x₀) U := by
  let A : Set U := boundaryMaximumLevelSet U u (u x₀)
  have hA_open : IsOpen A := by
    simpa [A] using
      isOpen_boundaryMaximumLevelSet_of_meanValue hU_open hu_cont hmax hmean
  have hA_closed : IsClosed A := by
    simpa [A] using
      isClosed_boundaryMaximumLevelSet (hu_cont.mono subset_closure)
  have hA_nonempty : A.Nonempty := by
    refine ⟨⟨x₀, hx₀⟩, ?_⟩
    simp [A, boundaryMaximumLevelSet]
  letI : PreconnectedSpace U := Subtype.preconnectedSpace hU_preconnected
  have hA_univ : A = Set.univ :=
    (show IsClopen A from ⟨hA_closed, hA_open⟩).eq_univ hA_nonempty
  intro y hy
  have hyA : (⟨y, hy⟩ : U) ∈ A := by
    rw [hA_univ]
    exact Set.mem_univ _
  simpa [A, boundaryMaximumLevelSet] using hyA

/-! ## 1. From constancy on `U` to constancy on `closure U` -/

/-- If the strong maximum principle makes `u` constant on `U`, continuity on
`closure U` propagates the equality to the closure.

This is the formal form of the density/continuity step

`u = u x₀ on U  ⇒  u = u x₀ on closure U`.
-/
theorem eqOn_closure_const_of_harmonic_maximum {n : ℕ}
    {U : Set (E n)} {u : E n → ℝ} {x₀ : E n}
    (hU_preconnected : IsPreconnected U)
    (hU_open : IsOpen U)
    (hu : InnerProductSpace.HarmonicContOnCl u U)
    (hx₀ : x₀ ∈ U)
    (hmax : AttainsMaxOnClosure u U x₀)
    (hmean : HasBallMeanValuePropertyOn u U) :
    Set.EqOn u (fun _ : E n => u x₀) (closure U) := by
  have hu_U : Set.EqOn u (fun _ : E n => u x₀) U := by
    exact eqOn_const_of_meanValue_of_isPreconnected_boundary
      hU_preconnected hU_open hu.continuousOn hx₀ hmax hmean
  exact hu_U.of_subset_closure
    hu.continuousOn continuousOn_const subset_closure Subset.rfl

/-! ## 2. A bounded domain in positive dimension has nonempty frontier -/

/-- A nonempty bounded subset of positive-dimensional Euclidean space cannot
be the whole space, hence its frontier is nonempty.

The hypothesis `0 < n` is necessary.  For `n = 0`, `E 0` is a singleton and
the nonempty open bounded set `univ` has empty frontier.
-/
lemma frontier_nonempty_of_nonempty_bounded {n : ℕ} {U : Set (E n)}
    (hn : 0 < n)
    (hU_nonempty : U.Nonempty)
    (hU_bounded : Bornology.IsBounded U) :
    (frontier U).Nonempty := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hU_ne_univ : U ≠ Set.univ := by
    intro hU_univ
    apply NormedSpace.unbounded_univ ℝ (E n)
    simpa [hU_univ] using hU_bounded
  exact nonempty_frontier_iff.mpr ⟨hU_nonempty, hU_ne_univ⟩

/-! ## 3. The maximum value is attained on the frontier -/

/-- Predicate-level version of

`max_(frontier U) u = max_(closure U) u = u x₀`.

`IsMaximumValueOnFrontier u U (u x₀)` says both that `u x₀` is attained
on `frontier U` and that every frontier value is at most `u x₀`.
-/
theorem isMaximumValueOnFrontier_of_harmonic_maximum {n : ℕ}
    {U : Set (E n)} {u : E n → ℝ} {x₀ : E n}
    (hn : 0 < n)
    (hU_nonempty : U.Nonempty)
    (hU_preconnected : IsPreconnected U)
    (hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (hu : InnerProductSpace.HarmonicContOnCl u U)
    (hx₀ : x₀ ∈ U)
    (hmax : AttainsMaxOnClosure u U x₀)
    (hmean : HasBallMeanValuePropertyOn u U) :
    IsMaximumValueOnFrontier u U (u x₀) := by
  have hu_closure :
      Set.EqOn u (fun _ : E n => u x₀) (closure U) :=
    eqOn_closure_const_of_harmonic_maximum
      hU_preconnected hU_open hu hx₀ hmax hmean
  rcases frontier_nonempty_of_nonempty_bounded
      hn hU_nonempty hU_bounded with ⟨z, hz⟩
  constructor
  · -- The value `u x₀` is attained at the frontier point `z`.
    refine ⟨z, hz, ?_⟩
    exact hu_closure (frontier_subset_closure hz)
  · -- Every value on the frontier is in fact equal to `u x₀`.
    rintro _ ⟨y, hy, rfl⟩
    exact (hu_closure (frontier_subset_closure hy)).le

/-! ## 4. Requested API: literal equality of the two suprema -/

/-- General-dimensional requested API.

The left-hand side formalizes `max_(∂U) u` and the right-hand side formalizes
`max_(closure U) u`.  Both sets have an actual greatest value, so the use of
`sSup` here really denotes a maximum rather than a merely limiting supremum.

The additional `hmean` input is temporary and necessary until a general `ℝⁿ`
ball mean-value theorem is connected to `HarmonicOnNhd`.
-/
theorem requested_boundary_maximum_api {n : ℕ}
    {U : Set (E n)} {u : E n → ℝ} {x₀ : E n}
    (hn : 0 < n)
    (hU_nonempty : U.Nonempty)
    (hU_preconnected : IsPreconnected U)
    (hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (hu : InnerProductSpace.HarmonicContOnCl u U)
    (hx₀ : x₀ ∈ U)
    (hmax : AttainsMaxOnClosure u U x₀)
    (hmean : HasBallMeanValuePropertyOn u U) :
    sSup (u '' frontier U) = sSup (u '' closure U) := by
  have hfrontier : IsMaximumValueOnFrontier u U (u x₀) :=
    isMaximumValueOnFrontier_of_harmonic_maximum
      hn hU_nonempty hU_preconnected hU_bounded hU_open
      hu hx₀ hmax hmean
  have hclosure : IsGreatest (u '' closure U) (u x₀) := by
    constructor
    · exact ⟨x₀, hmax.1, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hmax.2 hy
  exact hfrontier.csSup_eq.trans hclosure.csSup_eq.symm

/-! ## 5. Dimension two: no separate mean-value assumption -/

/-- In two dimensions, `ComplexBallMeanValue.lean` supplies `hmean`
automatically, so this wrapper has exactly the mathematical inputs listed in
the question.
-/
theorem requested_boundary_maximum_api_two
    {U : Set (E 2)} {u : E 2 → ℝ} {x₀ : E 2}
    (hU_nonempty : U.Nonempty)
    (hU_preconnected : IsPreconnected U)
    (hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (hu : InnerProductSpace.HarmonicContOnCl u U)
    (hx₀ : x₀ ∈ U)
    (hmax : AttainsMaxOnClosure u U x₀) :
    sSup (u '' frontier U) = sSup (u '' closure U) := by
  apply requested_boundary_maximum_api (n := 2) (by norm_num)
      hU_nonempty hU_preconnected hU_bounded hU_open hu hx₀ hmax
  exact harmonic_hasBallMeanValuePropertyOn_two hu.harmonicOnNhd

end StrongMaximumPrinciple
