import LocalMaximumBall
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# From circle averages to the two-dimensional ball mean-value property

`HarmonicOnNhd.circleAverage_eq` is the complex-plane circle mean-value
theorem already present in mathlib.  This file combines it with mathlib's
rigorous polar-coordinate change of variables
`Complex.integral_comp_polarCoord_symm` and obtains the area mean-value
identity on a disc.

The final theorem specializes
`StrongMaximumPrinciple.requested_harmonic_local_constancy_api` to dimension
two.  Its caller no longer has to supply the temporary `hmean` argument.
-/

open Set Metric MeasureTheory Laplacian
open scoped InnerProductSpace Real Topology

noncomputable section

namespace StrongMaximumPrinciple

/-! ## 1. The isometry `ℂ ≃ ℝ²` -/

/-- The standard real-linear isometry from the complex plane to `E 2`. -/
abbrev complexToE2 : ℂ ≃ₗᵢ[ℝ] E 2 :=
  Complex.orthonormalBasisOneI.repr

/-! ## 2. Harmonicity is unchanged by an orthogonal coordinate change -/

/-- The Laplacian commutes with precomposition by a real linear isometry.

This small bridge is needed because mathlib's circle theorem is stated on
`ℂ`, whereas `LocalMaximumBall.lean` uses `EuclideanSpace ℝ (Fin 2)`.
-/
lemma laplacian_comp_linearIsometryEquiv
    {X Y F : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : X ≃ₗᵢ[ℝ] Y) (f : Y → F) :
    Δ (f ∘ e) = Δ f ∘ e := by
  funext x
  rw [congrFun
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        (f ∘ e) (stdOrthonormalBasis ℝ X)) x]
  change (∑ i, iteratedFDeriv ℝ 2 (f ∘ e) x
      ![(stdOrthonormalBasis ℝ X) i, (stdOrthonormalBasis ℝ X) i]) = Δ f (e x)
  rw [congrFun
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        f ((stdOrthonormalBasis ℝ X).map e)) (e x)]
  apply Finset.sum_congr rfl
  intro i _hi
  have hcomp :=
    e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right
      (s := (Set.univ : Set Y)) f uniqueDiffOn_univ (mem_univ (e x)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hcomp
  have hcomp' :
      iteratedFDeriv ℝ 2 (f ∘ e) x =
        (iteratedFDeriv ℝ 2 f (e x)).compContinuousLinearMap
          (fun _ => e.toContinuousLinearEquiv.toContinuousLinearMap) := by
    simpa only [LinearIsometryEquiv.coe_coe] using hcomp
  rw [hcomp']
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  fin_cases j <;> simp

/-- Pointwise harmonicity is preserved by a real linear isometry. -/
lemma harmonicAt_comp_linearIsometryEquiv
    {X Y F : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e : X ≃ₗᵢ[ℝ] Y} {f : Y → F} {x : X}
    (hf : InnerProductSpace.HarmonicAt f (e x)) :
    InnerProductSpace.HarmonicAt (f ∘ e) x := by
  constructor
  · exact hf.1.comp_continuousLinearMap e.toContinuousLinearMap
  · rw [laplacian_comp_linearIsometryEquiv e f]
    change ∀ᶠ y in nhds x, (Δ f) (e y) = 0
    exact e.continuous.continuousAt.eventually hf.2

/-- Setwise version of harmonicity invariance. -/
lemma harmonicOnNhd_comp_linearIsometryEquiv
    {X Y F : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e : X ≃ₗᵢ[ℝ] Y} {f : Y → F} {s : Set Y}
    (hf : InnerProductSpace.HarmonicOnNhd f s) :
    InnerProductSpace.HarmonicOnNhd (f ∘ e) (e ⁻¹' s) := by
  intro x hx
  exact harmonicAt_comp_linearIsometryEquiv (hf (e x) hx)

/-! ## 3. Polar-coordinate integral over a complex disc -/

/-- An angular integral over `(-π, π)` is `2π` times the circle average. -/
private lemma integral_Ioo_neg_pi_pi_eq_two_pi_mul_circleAverage
    {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ} :
    (∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap c ρ θ)) =
      (2 * Real.pi) * Real.circleAverage f c ρ := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  rw [Real.circleAverage_eq_integral_add (f := f) (c := c) (R := ρ) (-Real.pi)]
  rw [intervalIntegral.integral_comp_add_right
    (fun θ => f (circleMap c ρ θ)) (-Real.pi)]
  have hπ : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [zero_add, hπ]
  simp [smul_eq_mul, mul_assoc]

/-- Polar-coordinate formula restricted to the disc `ball c r`.

The proof uses the global change-of-variables theorem from mathlib and then
restricts its radial coordinate to `0 < ρ < r`.  In particular, the Jacobian
factor `ρ` and all zero-measure endpoint issues are handled inside the proof;
they are not additional assumptions of the API.
-/
private lemma integral_ball_eq_polar
    {f : ℂ → ℝ} {c : ℂ} {r : ℝ} (_hr : 0 < r)
    (hf_cont : ContinuousOn f (closedBall c r)) :
    (∫ z in ball c r, f z) =
      ∫ ρ in Ioo (0 : ℝ) r,
        ∫ θ in Ioo (-Real.pi) Real.pi,
          ρ * f (circleMap c ρ θ) := by
  let P : ℝ × ℝ → ℝ := fun p =>
    p.1 * f (c + Complex.polarCoord.symm p)

  -- `P` is integrable on the bounded polar rectangle.
  have hP_cont :
      ContinuousOn P (Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi) := by
    apply ContinuousOn.mul continuous_fst.continuousOn
    apply hf_cont.comp
    · have hcontinuous : Continuous (fun p : ℝ × ℝ =>
          c + p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I)) := by
        fun_prop
      simpa [Complex.polarCoord_symm_apply] using hcontinuous.continuousOn
    · intro p hp
      rw [mem_closedBall]
      simpa [dist_eq_norm, Complex.norm_polarCoord_symm,
        abs_of_nonneg hp.1.1] using hp.1.2

  have hP_integrable_closed :
      IntegrableOn P (Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi) :=
    hP_cont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

  have hP_integrable :
      IntegrableOn P (Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi) :=
    hP_integrable_closed.mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

  -- First translate the disc center to zero.
  have htranslate :
      (∫ z in ball c r, f z) = ∫ z in ball (0 : ℂ) r, f (c + z) := by
    calc
      (∫ z in ball c r, f z) =
          ∫ z, (ball c r).indicator f z :=
        (integral_indicator measurableSet_ball).symm
      _ = ∫ z, (ball c r).indicator f (c + z) :=
        (integral_add_left_eq_self ((ball c r).indicator f) c).symm
      _ = ∫ z, (ball (0 : ℂ) r).indicator (fun z => f (c + z)) z := by
        congr 1
        funext z
        by_cases hz : z ∈ ball (0 : ℂ) r
        · rw [indicator_of_mem hz]
          rw [indicator_of_mem]
          simpa [mem_ball, dist_eq_norm] using hz
        · rw [indicator_of_notMem hz]
          rw [indicator_of_notMem]
          simpa [mem_ball, dist_eq_norm] using hz
      _ = ∫ z in ball (0 : ℂ) r, f (c + z) :=
        integral_indicator measurableSet_ball

  -- Apply mathlib's rigorous polar-coordinate change of variables.
  let g : ℂ → ℝ :=
    (ball (0 : ℂ) r).indicator (fun z => f (c + z))

  have hpolar_global :
      (∫ p in Complex.polarCoord.target,
          p.1 • g (Complex.polarCoord.symm p)) = ∫ z, g z :=
    Complex.integral_comp_polarCoord_symm g

  have hpolar_restrict :
      (∫ p in Complex.polarCoord.target,
          p.1 • g (Complex.polarCoord.symm p)) =
        ∫ p in Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi, P p := by
    let T : Set (ℝ × ℝ) := {p | p.1 < r}
    have hT : MeasurableSet T := measurableSet_lt measurable_fst measurable_const
    calc
      (∫ p in Complex.polarCoord.target,
          p.1 • g (Complex.polarCoord.symm p)) =
          ∫ p in Complex.polarCoord.target, T.indicator P p := by
        apply setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
        intro p hp
        rw [Complex.polarCoord_target] at hp
        have hp0 : 0 < p.1 := hp.1
        by_cases hpr : p.1 < r
        · have hpT : p ∈ T := hpr
          rw [indicator_of_mem hpT]
          simp [g, P, indicator_of_mem, mem_ball, abs_of_pos hp0, hpr, smul_eq_mul]
        · have hpT : p ∉ T := hpr
          rw [indicator_of_notMem hpT]
          simp [g, indicator_of_notMem, mem_ball, abs_of_pos hp0, hpr, smul_eq_mul]
      _ = ∫ p in Complex.polarCoord.target ∩ T, P p :=
        setIntegral_indicator hT
      _ = ∫ p in Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi, P p := by
        rw [show Complex.polarCoord.target ∩ T =
            Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi by
          ext p
          simp [T, Complex.polarCoord_target, and_left_comm, and_comm, and_assoc]]

  have hFubini :
      (∫ p in Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi, P p) =
        ∫ ρ in Ioo (0 : ℝ) r,
          ∫ θ in Ioo (-Real.pi) Real.pi, P (ρ, θ) := by
    rw [Measure.volume_eq_prod]
    exact MeasureTheory.setIntegral_prod P hP_integrable

  calc
    (∫ z in ball c r, f z) = ∫ z, g z := by
      rw [htranslate]
      simpa [g] using
        (integral_indicator (f := fun z : ℂ => f (c + z)) measurableSet_ball).symm
    _ = ∫ p in Complex.polarCoord.target,
          p.1 • g (Complex.polarCoord.symm p) := hpolar_global.symm
    _ = ∫ p in Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi, P p :=
      hpolar_restrict
    _ = ∫ ρ in Ioo (0 : ℝ) r,
          ∫ θ in Ioo (-Real.pi) Real.pi, P (ρ, θ) := hFubini
    _ = ∫ ρ in Ioo (0 : ℝ) r,
          ∫ θ in Ioo (-Real.pi) Real.pi,
            ρ * f (circleMap c ρ θ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro ρ _hρ
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ _hθ
      simp [P, circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]

/-! ## 4. Circle mean value implies disc mean value -/

/-- The area mean-value identity for real-valued harmonic functions on `ℂ`.

This is the proved two-dimensional `hmean` theorem:

`∫ z in ball c r, f z = π r² f(c)`.
-/
theorem harmonicOnNhd_integral_ball_eq_pi_mul_sq
    {f : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f (closedBall c r))
    (hr : 0 < r) :
    (∫ z in ball c r, f z) = Real.pi * r ^ 2 * f c := by
  rw [integral_ball_eq_polar hr hf.continuousOn]
  calc
    (∫ ρ in Ioo (0 : ℝ) r,
        ∫ θ in Ioo (-Real.pi) Real.pi,
          ρ * f (circleMap c ρ θ)) =
        ∫ ρ in Ioo (0 : ℝ) r, ρ * ((2 * Real.pi) * f c) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro ρ hρ
      change (∫ θ in Ioo (-Real.pi) Real.pi,
          ρ * f (circleMap c ρ θ)) = ρ * ((2 * Real.pi) * f c)
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [integral_Ioo_neg_pi_pi_eq_two_pi_mul_circleAverage]
      rw [HarmonicOnNhd.circleAverage_eq]
      simpa [abs_of_pos hρ.1] using
        hf.mono (closedBall_subset_closedBall hρ.2.le)
    _ = Real.pi * r ^ 2 * f c := by
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
      rw [← intervalIntegral.integral_of_le hr.le]
      rw [intervalIntegral.integral_mul_const, integral_id]
      ring

/-! ## 5. Supply `hmean` on `E 2` and call the existing local API -/

/-- Harmonic functions on `E 2` satisfy the temporary ball mean-value
interface from `LocalMaximumBall.lean`.
-/
theorem harmonic_hasBallMeanValuePropertyOn_two
    {U : Set (E 2)} {u : E 2 → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u U) :
    HasBallMeanValuePropertyOn u U := by
  intro x hx r hr hclosed
  let e : ℂ ≃ₗᵢ[ℝ] E 2 := complexToE2
  let c : ℂ := e.symm x
  let f : ℂ → ℝ := u ∘ e

  have hf : InnerProductSpace.HarmonicOnNhd f (closedBall c r) := by
    intro z hz
    have hez : e z ∈ U := by
      apply hclosed
      rw [mem_closedBall] at hz ⊢
      calc
        dist (e z) x = dist (e z) (e (e.symm x)) := by rw [e.apply_symm_apply]
        _ = dist z (e.symm x) := e.dist_map z (e.symm x)
        _ ≤ r := hz
    exact harmonicAt_comp_linearIsometryEquiv (hu (e z) hez)

  have hcomplex :
      (∫ z in ball c r, f z) = Real.pi * r ^ 2 * f c :=
    harmonicOnNhd_integral_ball_eq_pi_mul_sq hf hr

  have hintegral :
      (∫ y in ball x r, u y) = ∫ z in ball c r, f z := by
    symm
    simpa [c, f] using
      (LinearIsometryEquiv.measurePreserving e).setIntegral_preimage_emb
        e.toHomeomorph.toMeasurableEquiv.measurableEmbedding u (ball x r)

  have hfc : f c = u x := by
    change u (e (e.symm x)) = u x
    rw [e.apply_symm_apply]

  have hvolume : ballVolume x r = Real.pi * r ^ 2 := by
    rw [ballVolume, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul]
    simp [hr.le, Real.pi_pos.le]
    ring

  rw [hintegral, hcomplex, hfc, hvolume]

/-- Requested local-constancy theorem in dimension two, with no `hmean`
argument.  This is the wrapper requested in the question: the proof constructs
`hmean` above and passes it to `requested_harmonic_local_constancy_api`.
-/
theorem requested_harmonic_local_constancy_api_two
    {U : Set (E 2)} {u : E 2 → ℝ} {x₀ : E 2}
    (hU_nonempty : U.Nonempty)
    (hU_preconnected : IsPreconnected U)
    (hU_bounded : Bornology.IsBounded U)
    (hU_open : IsOpen U)
    (hu : InnerProductSpace.HarmonicContOnCl u U)
    (hx₀ : x₀ ∈ U)
    (hmax : AttainsMaxOnClosure u U x₀) :
    ∃ r : ℝ, 0 < r ∧ closedBall x₀ r ⊆ U ∧
      ∀ y ∈ ball x₀ r, u y = u x₀ := by
  apply requested_harmonic_local_constancy_api
      hU_nonempty hU_preconnected hU_bounded hU_open hu hx₀ hmax
  exact harmonic_hasBallMeanValuePropertyOn_two hu.harmonicOnNhd

end StrongMaximumPrinciple
