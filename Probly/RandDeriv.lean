import Mathlib.Analysis.Calculus.FDeriv.Basic

import Probly.DRand
import Probly.RewriteBy

namespace Probly

open MeasureTheory ENNReal BigOperators Finset

def randDeriv {X} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y} [MeasurableSpace Y]
    (f : X → Rand Y) (x dx : X) : DRand Y := {
  -- differentiate `f` as a functin from `X` to the space of finite measures
  -- with finite total variation 
  dμPos := sorry
  dμNeg := sorry
  dμ_real_zero := sorry
}

def randFwdDeriv {X} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y} [MeasurableSpace Y]
    (f : X → Rand Y) (x dx : X) : Rand Y × DRand Y := (f x, randDeriv f x dx)

opaque RandDifferentiable {X} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y} [MeasurableSpace Y]
    (f : X → Rand Y) : Prop 

-- this has to exist somewhere
/- scoped instance {X} [NormedAddCommGroup X] [NormedSpace ℝ X] : MeasurableSpace X := by (try infer_instance); sorry
 -/

instance {X} [MeasurableSpace X] : Zero (DRand X) := sorry
instance {X} [MeasurableSpace X] : Add (DRand X) := sorry
instance {X} [MeasurableSpace X] : SMul ℝ (DRand X) := sorry


section RandDeriv

variable 
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]


@[simp]
theorem randDeriv_pure (x : W → X) (hx : Differentiable ℝ x) : 
    randDeriv (fun w => Rand.pure (x w))
    =
    fun w dw => DRand.pure (fderiv ℝ x w dw) := sorry


@[simp]
theorem randDeriv_const (a : Rand α) : 
    randDeriv (fun w : W => a)
    =
    fun w dw => 0 := sorry


@[simp]
theorem randDeriv_bind (x : W → Rand α) (f : W → α → Rand β) 
    (hx : RandDifferentiable x) (hf : ∀ x, RandDifferentiable (f · x)) : 
    randDeriv (fun w => (x w).bind (f w ·)) 
    =
    fun w dw => (randDeriv x w dw).bind (f w · )
                +
                (x w).dbind (fun x => randDeriv (f · x) w dw) := sorry

@[simp]
theorem randFwdDeriv_bind (x : W → Rand α) (f : W → α → Rand β) 
    (hx : RandDifferentiable x) (hf : ∀ x, RandDifferentiable (f · x)) : 
    randFwdDeriv (fun w => (x w).bind (f w ·)) 
    =
    fun w dw => bind₂ (randFwdDeriv x w dw) (fun a => randFwdDeriv (f · a) w dw) := by

  unfold bind₂ randFwdDeriv
  funext w dw
  simp (disch:=first | apply hx | apply hf)
  


/-- P(n) = x^n * exp (-x) / n! -/
def randNatPoisson (x : ℝ) : Rand ℕ := sorry


/-- DP(n) = (n * x^(n-1) - x^n) * exp (-x) / n! -/
def drandNatPoisson (x : ℝ) : DRand ℕ := sorry


def flip (x : ℝ) : Rand Bool := sorry
def dflip : DRand Bool := sorry


@[simp]
theorem randDeriv_poisson : randDeriv randNatPoisson = fun x dx => dx • drandNatPoisson x := sorry


@[simp]
theorem randDeriv_ite {c} [Decidable c]
  (t f : W → Rand α) (ht : RandDifferentiable t) (hf : RandDifferentiable f)
  : randDeriv (fun w => if c then t w else f w) 
    = 
    fun w dw => if c then randDeriv t w dw else randDeriv f w dw := sorry

@[simp]
theorem randFwdDeriv_ite {c} [dec : Decidable c]
  (t f : W → Rand α) (ht : RandDifferentiable t) (hf : RandDifferentiable f)
  : randFwdDeriv (fun w => if c then t w else f w) 
    = 
    fun w dw => if c then randFwdDeriv t w dw else randFwdDeriv f w dw := by
  
  unfold randFwdDeriv; aesop
  



@[simp]
theorem randDeriv_flip : randDeriv flip = fun x dx => dx•dflip := sorry

noncomputable
def draw (x : ℝ): Rand ℝ :=
  let b ~ (flip x)
  if b then
    (0 : ℝ)
  else
    (- x / (2:ℝ))

macro "ad" : conv => `(conv| simp (disch:=sorry) only [randFwdDeriv_bind,randDeriv_pure, randDeriv_bind,randDeriv_poisson,randDeriv_const, randDeriv_flip,randDeriv_ite])

set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.rewrite true in
#check randFwdDeriv draw
  rewrite_by
  unfold draw
  ad
  simp (disch:=sorry) only [randDeriv_pure] 
  