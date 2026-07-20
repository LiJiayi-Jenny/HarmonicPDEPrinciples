import BoundaryMaximum

/-!
# Uniqueness for the Poisson--Dirichlet problem

For a nonempty, bounded, preconnected open set `U ⊆ ℝⁿ`, consider

`-Δu = f` on `U`, and `u = g` on `frontier U`.

If `u₁` and `u₂` are two solutions, their difference `w = u₁ - u₂`
is harmonic and vanishes on the frontier.  Applying the boundary maximum
argument to both `w` and `-w` gives `w ≤ 0` and `-w ≤ 0` on `closure U`,
so `w = 0` there.

Because the solutions below are represented by ambient functions
`E n → ℝ`, the correct uniqueness conclusion is `EqOn u₁ u₂ (closure U)`.
The equation and boundary data impose no conditions outside `closure U`, so
literal equality of the ambient representatives would be false in general.

As in the preceding files, the general-dimensional API is conditional on a
ball mean-value provider.  The final two-dimensional theorem discharges that
condition using `ComplexBallMeanValue.lean` through `BoundaryMaximum.lean`.
-/

open Set Filter
open Laplacian

noncomputable section

namespace StrongMaximumPrinciple

/-! ## 1. The Poisson--Dirichlet solution predicate -/

/-- `u` is a classical solution of the Poisson--Dirichlet problem on `U`.

* `contDiffOn` formalizes `u ∈ C²(U)`;
* `continuousOn_closure` formalizes `u ∈ C(closure U)`;
* `poisson_eq` is `-Δu = f` on `U`;
* `boundary_eq` is `u = g` on `frontier U`.
-/
structure IsPoissonDirichletSolution {n : ℕ}
    (U : Set (E n)) (f g u : E n → ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ 2 u U
  continuousOn_closure : ContinuousOn u (closure U)
  poisson_eq : ∀ x ∈ U, -(Δ u) x = f x
  boundary_eq : Set.EqOn u g (frontier U)

/-- There is at most one solution *on `closure U`*.

This is the appropriate uniqueness notion for ambient representatives:
solutions may be changed arbitrarily outside `closure U` without changing the
boundary-value problem.
-/
def HasAtMostOnePoissonDirichletSolution {n : ℕ}
    (U : Set (E n)) (f g : E n → ℝ) : Prop :=
  ∀ {u₁ u₂ : E n → ℝ},
    IsPoissonDirichletSolution U f g u₁ →
    IsPoissonDirichletSolution U f g u₂ →
    Set.EqOn u₁ u₂ (closure U)

/-! ## 2. The temporary general-dimensional mean-value provider -/

/-- Every real-valued harmonic function on `U` has the ball mean-value
property used by `LocalMaximumBall.lean`.

This separates the still-missing general `ℝⁿ` mean-value theorem from the
uniqueness argument itself.
-/
def HasHarmonicBallMeanValuePropertyOn {n : ℕ} (U : Set (E n)) : Prop :=
  ∀ {v : E n → ℝ},
    InnerProductSpace.HarmonicOnNhd v U →
      HasBallMeanValuePropertyOn v U

/-- The mean-value property is preserved by negation. -/
lemma HasBallMeanValuePropertyOn.neg {n : ℕ}
    {U : Set (E n)} {v : E n → ℝ}
    (hv : HasBallMeanValuePropertyOn v U) :
    HasBallMeanValuePropertyOn (-v) U := by
  intro x hx r hr hclosed
  have h := hv hx hr hclosed
  simp only [Pi.neg_apply]
  rw [MeasureTheory.integral_neg, h]
  simp

/-! ## 3. The difference of two Poisson solutions is harmonic -/

/-- If two `C²` functions solve the same Poisson equation, their difference
is harmonic.  Continuity on `closure U` is preserved by subtraction.
-/
lemma harmonicContOnCl_sub_of_poissonSolutions {n : ℕ}
    {U : Set (E n)} {f g u₁ u₂ : E n → ℝ}
    (hU_open : IsOpen U)
    (hu₁ : IsPoissonDirichletSolution U f g u₁)
    (hu₂ : IsPoissonDirichletSolution U f g u₂) :
    InnerProductSpace.HarmonicContOnCl (u₁ - u₂) U := by
  constructor
  · intro x hx
    have hu₁x : ContDiffAt ℝ 2 u₁ x :=
      (hu₁.contDiffOn x hx).contDiffAt (hU_open.mem_nhds hx)
    have hu₂x : ContDiffAt ℝ 2 u₂ x :=
      (hu₂.contDiffOn x hx).contDiffAt (hU_open.mem_nhds hx)

    constructor
    · exact hu₁x.sub hu₂x
    · filter_upwards
        [hu₁x.laplacian_sub_nhds hu₂x, hU_open.mem_nhds hx]
        with y hlap hy
      rw [hlap]
      have hΔ : (Δ u₁) y = (Δ u₂) y := by
        linarith [hu₁.poisson_eq y hy, hu₂.poisson_eq y hy]
      simp [hΔ]
  · exact hu₁.continuousOn_closure.sub hu₂.continuousOn_closure

/-- The difference of two solutions is zero on `frontier U`. -/
lemma sub_eq_zero_on_frontier_of_poissonSolutions {n : ℕ}
    {U : Set (E n)} {f g u₁ u₂ : E n → ℝ}
    (hu₁ : IsPoissonDirichletSolution U f g u₁)
    (hu₂ : IsPoissonDirichletSolution U f g u₂) :
    Set.EqOn (u₁ - u₂) (fun _ : E n => 0) (frontier U) := by
  intro x hx
  simp only [Pi.sub_apply]
  rw [hu₁.boundary_eq hx, hu₂.boundary_eq hx]
  simp

/-! ## 4. Zero boundary values force a harmonic function to vanish -/

/-- One-sided maximum principle for zero boundary data.

The continuous function `v` attains its maximum on the compact set
`closure U`.  If a maximizing point is on the frontier, its value is zero.
If it lies in `U`, `BoundaryMaximum.lean` shows that the same maximum value is
attained on the frontier, and is therefore again zero.
-/
theorem le_zero_on_closure_of_harmonic_zero_on_frontier {n : ℕ}
    {U : Set (E n)} {v : E n → ℝ}
    (hn : 0 < n)
    (hU_nonempty : U.Nonempty)
    (hU_preconnected : IsPreconnected U)
    (hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (hv : InnerProductSpace.HarmonicContOnCl v U)
    (hv_zero : Set.EqOn v (fun _ : E n => 0) (frontier U))
    (hmean : HasBallMeanValuePropertyOn v U) :
    ∀ x ∈ closure U, v x ≤ 0 := by
  obtain ⟨xMax, hxMax_closure, hxMax⟩ :=
    hU_bounded.isCompact_closure.exists_isMaxOn
      hU_nonempty.closure hv.continuousOn

  have hAttains : AttainsMaxOnClosure v U xMax := by
    refine ⟨hxMax_closure, ?_⟩
    intro y hy
    exact hxMax hy

  have hv_xMax : v xMax = 0 := by
    rw [closure_eq_self_union_frontier U, mem_union] at hxMax_closure
    rcases hxMax_closure with hxMax_U | hxMax_frontier
    · have hfrontier : IsMaximumValueOnFrontier v U (v xMax) :=
        isMaximumValueOnFrontier_of_harmonic_maximum
          hn hU_nonempty hU_preconnected hU_bounded hU_open
          hv hxMax_U hAttains hmean
      rcases hfrontier.1 with ⟨z, hz, hz_value⟩
      exact hz_value.symm.trans (hv_zero hz)
    · exact hv_zero hxMax_frontier

  intro x hx
  exact (hxMax hx).trans_eq hv_xMax

/-- A harmonic function with zero frontier values is zero on all of
`closure U`.  We apply the preceding one-sided theorem to both `v` and `-v`.
-/
theorem eq_zero_on_closure_of_harmonic_zero_on_frontier {n : ℕ}
    {U : Set (E n)} {v : E n → ℝ}
    (hn : 0 < n)
    (hU_nonempty : U.Nonempty)
    (hU_preconnected : IsPreconnected U)
    (hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (hv : InnerProductSpace.HarmonicContOnCl v U)
    (hv_zero : Set.EqOn v (fun _ : E n => 0) (frontier U))
    (hmean : HasBallMeanValuePropertyOn v U) :
    Set.EqOn v (fun _ : E n => 0) (closure U) := by
  have hv_nonpos := le_zero_on_closure_of_harmonic_zero_on_frontier
    hn hU_nonempty hU_preconnected hU_bounded hU_open hv hv_zero hmean

  have hneg_zero :
      Set.EqOn (-v) (fun _ : E n => 0) (frontier U) := by
    intro x hx
    simp [hv_zero hx]

  have hneg_nonpos := le_zero_on_closure_of_harmonic_zero_on_frontier
    hn hU_nonempty hU_preconnected hU_bounded hU_open
      hv.neg hneg_zero hmean.neg

  intro x hx
  have h₁ := hv_nonpos x hx
  have h₂ := hneg_nonpos x hx
  change -v x ≤ 0 at h₂
  linarith

/-! ## 5. Requested general-dimensional uniqueness API -/

/-- Conditional general `ℝⁿ` uniqueness theorem.

Continuity of `f` and `g` is retained in the signature to match the
mathematical problem, although uniqueness itself only uses that the two
solutions have the same right-hand side and the same boundary values.
-/
theorem requested_poisson_dirichlet_uniqueness_api {n : ℕ}
    {U : Set (E n)} {f g : E n → ℝ}
    (hn : 0 < n)
    (hU_nonempty : U.Nonempty)
    (hU_preconnected : IsPreconnected U)
    (hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (_hf_cont : ContinuousOn f U)
    (_hg_cont : ContinuousOn g (frontier U))
    (hmean : HasHarmonicBallMeanValuePropertyOn U) :
    HasAtMostOnePoissonDirichletSolution U f g := by
  intro u₁ u₂ hu₁ hu₂
  let w : E n → ℝ := u₁ - u₂

  have hw : InnerProductSpace.HarmonicContOnCl w U := by
    simpa [w] using
      harmonicContOnCl_sub_of_poissonSolutions hU_open hu₁ hu₂

  have hw_zero : Set.EqOn w (fun _ : E n => 0) (frontier U) := by
    simpa [w] using sub_eq_zero_on_frontier_of_poissonSolutions hu₁ hu₂

  have hw_closure : Set.EqOn w (fun _ : E n => 0) (closure U) :=
    eq_zero_on_closure_of_harmonic_zero_on_frontier
      hn hU_nonempty hU_preconnected hU_bounded hU_open
      hw hw_zero (hmean hw.harmonicOnNhd)

  intro x hx
  have hxw := hw_closure hx
  change u₁ x - u₂ x = 0 at hxw
  exact sub_eq_zero.mp hxw

/-! ## 6. Dimension two: exact API with no mean-value input -/

/-- In dimension two, the circle-to-disc proof in
`ComplexBallMeanValue.lean` supplies the mean-value property automatically.
This theorem therefore has exactly the mathematical inputs requested by the
user (apart from the necessary positive-dimension fact, discharged by `2`).
-/
theorem requested_poisson_dirichlet_uniqueness_api_two
    {U : Set (E 2)} {f g : E 2 → ℝ}
    (hU_nonempty : U.Nonempty)
    (hU_preconnected : IsPreconnected U)
    (hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (hf_cont : ContinuousOn f U)
    (hg_cont : ContinuousOn g (frontier U)) :
    HasAtMostOnePoissonDirichletSolution U f g := by
  apply requested_poisson_dirichlet_uniqueness_api
      (n := 2) (by norm_num) hU_nonempty hU_preconnected
      hU_bounded hU_open hf_cont hg_cont
  intro v hv
  exact harmonic_hasBallMeanValuePropertyOn_two hv

end StrongMaximumPrinciple
