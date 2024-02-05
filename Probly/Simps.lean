import Probly.Init
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.Density
import Mathlib.Control.Random

open MeasureTheory ENNReal BigOperators Finset

namespace Probly


@[simp]
theorem ENNReal.ofReal_toReal (x : ℝ) : (ENNReal.ofReal x).toReal = x := sorry


variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]


@[rand_simp]
theorem integral_of_add_measure (f : α → X) (μ ν : Measure α) :
    ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν := sorry


@[rand_simp]
theorem integral_of_dirac (f : α → X) (μ ν : Measure α) :
    ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν := sorry
