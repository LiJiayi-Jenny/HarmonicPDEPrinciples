import BoundaryMaximum

/-!
# Comparison principle for harmonic functions

Let `U ⊆ ℝⁿ` be nonempty, bounded, preconnected and open.  If `u` and
`v` are harmonic on `U`, continuous on `closure U`, and `u ≤ v` on
`frontier U`, then `u ≤ v` on all of `closure U`.

The proof applies the boundary maximum argument to `w = u - v`.  Notice that
the harmonicity assumptions, not an inequality between the Laplacians, are
what make `BoundaryMaximum.lean` applicable: the difference of two harmonic
functions is harmonic.

For genuinely non-harmonic `C²` functions, the upper comparison principle
would require `Δu ≥ Δv` (equivalently `-Δu ≤ -Δv`).  The opposite
inequality written in the question does not imply `u ≤ v` in the interior.

The general-dimensional theorem keeps the same temporary mean-value input as
the earlier files.  The final two-dimensional wrapper supplies it
automatically from `ComplexBallMeanValue.lean`.
-/

open Set
open Laplacian

noncomputable section

namespace StrongMaximumPrinciple

/-! ## 1. A harmonic function nonpositive on the frontier is nonpositive
on the closure -/

/-- Weak boundary maximum principle in the form needed for comparison.

The function attains a maximum on the compact set `closure U`.  If a maximum
point belongs to `frontier U`, the boundary assumption finishes the proof.  If
it belongs to `U`, `isMaximumValueOnFrontier_of_harmonic_maximum` moves the
same maximum value to a frontier point.
-/
theorem le_zero_on_closure_of_harmonic_nonpositive_on_frontier {n : ℕ}
    {U : Set (E n)} {w : E n → ℝ}
    (hn : 0 < n)
    (hU_nonempty : U.Nonempty)
    (hU_preconnected : IsPreconnected U)
    (hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (hw : InnerProductSpace.HarmonicContOnCl w U)
    (hw_frontier : ∀ x ∈ frontier U, w x ≤ 0)
    (hmean : HasBallMeanValuePropertyOn w U) :
    ∀ x ∈ closure U, w x ≤ 0 := by
  obtain ⟨xMax, hxMax_closure, hxMax⟩ :=
    hU_bounded.isCompact_closure.exists_isMaxOn
      hU_nonempty.closure hw.continuousOn
  have hAttains : AttainsMaxOnClosure w U xMax := by
    refine ⟨hxMax_closure, ?_⟩
    intro y hy
    exact hxMax hy
  have hw_xMax : w xMax ≤ 0 := by
    rw [closure_eq_self_union_frontier U, mem_union] at hxMax_closure
    rcases hxMax_closure with hxMax_U | hxMax_frontier
    · have hfrontier : IsMaximumValueOnFrontier w U (w xMax) :=
        isMaximumValueOnFrontier_of_harmonic_maximum
          hn hU_nonempty hU_preconnected hU_bounded hU_open
          hw hxMax_U hAttains hmean
      rcases hfrontier.1 with ⟨z, hz, hz_value⟩
      simpa only [hz_value] using hw_frontier z hz
    · exact hw_frontier xMax hxMax_frontier
  intro x hx
  exact (hxMax hx).trans hw_xMax

/-! ## 2. Comparison without the redundant Laplacian inequality -/

/-- Comparison principle for two harmonic functions.

`HarmonicContOnCl` packages harmonicity (hence `C²` regularity) on `U` and
continuity on `closure U`.
-/
theorem harmonic_comparison_on_closure {n : ℕ}
    {U : Set (E n)} {u v : E n → ℝ}
    (hn : 0 < n)
    (hU_nonempty : U.Nonempty)
    (hU_preconnected : IsPreconnected U)
    (hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (hu : InnerProductSpace.HarmonicContOnCl u U)
    (hv : InnerProductSpace.HarmonicContOnCl v U)
    (huv_frontier : ∀ x ∈ frontier U, u x ≤ v x)
    (hmean : HasBallMeanValuePropertyOn (u - v) U) :
    ∀ x ∈ closure U, u x ≤ v x := by
  have hw : InnerProductSpace.HarmonicContOnCl (u - v) U := hu.sub hv
  have hw_frontier : ∀ x ∈ frontier U, (u - v) x ≤ 0 := by
    intro x hx
    simp only [Pi.sub_apply]
    linarith [huv_frontier x hx]
  have hw_nonpos := le_zero_on_closure_of_harmonic_nonpositive_on_frontier
    hn hU_nonempty hU_preconnected hU_bounded hU_open
      hw hw_frontier hmean
  intro x hx
  have hx_nonpos := hw_nonpos x hx
  change u x - v x ≤ 0 at hx_nonpos
  linarith

/-! ## 3. Requested API, retaining the stated Laplacian inequality -/

/-- API matching the input written in the question.

Because both functions are harmonic, `Δu = Δv = 0` on `U`; consequently
the supplied inequality `Δu ≤ Δv` is mathematically redundant.  It is kept
in this wrapper only so that the signature visibly matches the request.
-/
theorem requested_harmonic_comparison_api {n : ℕ}
    {U : Set (E n)} {u v : E n → ℝ}
    (hn : 0 < n)
    (hU_nonempty : U.Nonempty)
    (hU_preconnected : IsPreconnected U)
    (hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (hu : InnerProductSpace.HarmonicContOnCl u U)
    (hv : InnerProductSpace.HarmonicContOnCl v U)
    (_hΔ : ∀ x ∈ U, (Δ u) x ≤ (Δ v) x)
    (huv_frontier : ∀ x ∈ frontier U, u x ≤ v x)
    (hmean : HasBallMeanValuePropertyOn (u - v) U) :
    ∀ x ∈ closure U, u x ≤ v x := by
  exact harmonic_comparison_on_closure
    hn hU_nonempty hU_preconnected hU_bounded hU_open
      hu hv huv_frontier hmean

/-! ## 4. Dimension two: no separate mean-value input -/

/-- Two-dimensional comparison principle with exactly the requested
mathematical data.  The mean-value property of `u - v` is derived internally.
-/
theorem requested_harmonic_comparison_api_two
    {U : Set (E 2)} {u v : E 2 → ℝ}
    (hU_nonempty : U.Nonempty)
    (hU_preconnected : IsPreconnected U)
    (hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (hu : InnerProductSpace.HarmonicContOnCl u U)
    (hv : InnerProductSpace.HarmonicContOnCl v U)
    (hΔ : ∀ x ∈ U, (Δ u) x ≤ (Δ v) x)
    (huv_frontier : ∀ x ∈ frontier U, u x ≤ v x) :
    ∀ x ∈ closure U, u x ≤ v x := by
  apply requested_harmonic_comparison_api
      (n := 2) (by norm_num) hU_nonempty hU_preconnected
      hU_bounded hU_open hu hv hΔ huv_frontier
  exact harmonic_hasBallMeanValuePropertyOn_two (hu.sub hv).harmonicOnNhd

end StrongMaximumPrinciple
