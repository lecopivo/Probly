import Mathlib.MeasureTheory.Measure.VectorMeasure
import Mathlib.Logic.Function.Basic

import Probly.DRand

open MeasureTheory ENNReal BigOperators Finset

namespace Probly

structure FDRand (X : Type) [MeasurableSpace X] where
  val  : Rand X
  dval : DRand X

noncomputable
def randFwdDeriv {X} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y} [MeasurableSpace Y]
    (f : X → Rand Y) (x dx : X) : FDRand Y := ⟨f x, randDeriv f x dx⟩

instance {X} [MeasurableSpace X] : MeasurableSpace (FDRand X) := sorry

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]

open Rand

variable
  {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]


namespace FDRand

@[ext]
theorem ext (x y : FDRand X) : x.val = y.val → x.dval = x.dval → x = y := sorry


----------------------------------------------------------------------------------------------------
-- Monadic operations ------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

noncomputable
def fdpure (x dx : X) : FDRand X := {
  val  := pure x
  dval := dpure x dx
 }

noncomputable
def bind (x : FDRand X) (f : X → FDRand Y) : FDRand Y := {
  val  := x.val.bind (fun x' => (f x').val)
  dval := x.dval.bindDR (fun x' => (f x').val) +
          x.val.bindRD (fun x' => (f x').dval)
}

noncomputable
def join (x : FDRand (FDRand X)) : FDRand X := x.bind id


@[rand_simp,simp]
theorem bind_bind (x : FDRand X) (g : X → FDRand Y) (f : Y → FDRand Z) :
    bind (bind x g) f = bind x fun x' => bind (g x') f := by

  apply ext
  . simp (disch:=sorry) only [bind,rand_simp]
  . simp (disch:=sorry) only [bind,rand_simp]


@[rand_simp,simp]
theorem bind_pure (f : X → FDRand Y) (x dx : X) :
    (fdpure x dx).bind f
    =
    ⟨(f x).val, randDeriv (fun x' => (f x').val) x dx + (f x).dval⟩ := by

  simp only [bind,fdpure]
  apply ext
  . simp (disch:=sorry) only [rand_simp]
  . simp only [rand_simp]



----------------------------------------------------------------------------------------------------
-- Notation ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- we can't use do notation because Rand is not a monad right now (because of the [MeasurableSpace X] argument)
-- this is a small hack to recover it a bit
open Lean.Parser Term in
syntax withPosition("let" funBinder " ~~ " term semicolonOrLinebreak ppDedent(ppLine) term) : term
macro_rules
  | `(let $x ~~ $y; $b) => do Pure.pure (← `(Probly.FDRand.bind $y (fun $x => $b))).raw


open Lean Parser
@[app_unexpander FDRand.bind] def unexpandFDRandBind : Lean.PrettyPrinter.Unexpander

| `($(_) $y $f) =>
  match f.raw with
  | `(fun $x:term => $b) => do
    let s ←
      `(let $x ~~ $y
        $b)
    Pure.pure s.raw
  | _ => throw ()

| _ => throw ()



----------------------------------------------------------------------------------------------------
-- Expected Value and Change -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- noncomputable
-- def expectedValueAndChange (x : FDRand X) (φ : X → Y) : Y×Y := (x.val.E φ, x.dval.dE φ)

noncomputable
def fdE (x : FDRand X) (φ : X → Y) : Y×Y := (x.val.E φ, x.dval.dE φ)

@[rand_simp,simp]
theorem fdpure_fdE (x dx : X) (φ : X → Y) :
    (fdpure x dx).fdE φ = (φ x, fderiv ℝ φ x dx) := by

  simp (disch:=sorry) only [fdpure,fdE,rand_simp]


def finalize (x : (X×X)×(X×X)) : X×X := let y := x; (y.1.1,y.2.1+y.1.2)

@[rand_simp,simp]
theorem bind_fdE (x : FDRand X) (f : X → FDRand Y) (φ : Y → Z) :
    ((x.bind f).fdE φ)
    =
    finalize (x.fdE (fun x' => (f x').fdE φ)) := by

  simp (disch:=sorry) only [bind,fdpure,fdE,rand_simp]
  ext
  . simp (disch:=sorry) only [rand_simp]
    sorry -- just propagate projection to the integral
  . simp (disch:=sorry) only [rand_simp]
    sorry -- just propagate projection to the integral


@[rand_simp,simp]
theorem FDRand_mk_zero_fdE (x : Rand X) :
    (FDRand.mk x 0).fdE φ = (x.E φ, (0 : X)) := by
  simp [fdE,DRand.dE]
  apply testFunctionExtension_ext
  intro _ _
  simp [rand_simp,zero_smul]

theorem FDRand_mk_fdE (x : Rand X) (dx : DRand X) (φ : X → Y) :
    (FDRand.mk x dx).fdE φ = (x.E φ, dx.dE φ) := by rfl


def finalizeWith (p q : X → ℝ) (φ : X → Y) (x : X) : Y×Y := let y := φ x; (p x • y, q x • y)

theorem fdE_as_E {rx : FDRand X} {φ : X → Y} (rx' : Rand X) :
  rx.fdE φ = rx'.E (finalizeWith (rx.val.pdf' rx'.μ) (rx.dval.density rx'.μ) φ) := sorry

@[rand_simp,simp]
theorem ite_push_fdE {c} [Decidable c] (t f : FDRand X) (φ : X → Y) :
    (if c then t else f).fdE φ = if c then t.fdE φ else f.fdE φ := by
  if h : c then simp[h] else simp[h]

noncomputable
def fdmean (x : FDRand X) : X×X := x.fdE id

theorem expectedValueAndChange_as_fdmean (x : FDRand X) (φ : X → Y) :
    x.fdE φ = (x.bind (fun x' => fdpure (φ x') 0)).fdmean := by

  simp (disch:=sorry) only [rand_simp,mean,fdE,fdmean,bind,fdpure,id]
  simp


@[rand_simp,simp]
theorem finalize_pull_E (x : Rand ((X×X)×(X×X))) :
    finalize x.mean = (let x' ~ x; pure (finalize x')).mean := sorry
