import Probly.Flip

import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

import Mathlib.Tactic.LiftLets

open MeasureTheory ENNReal BigOperators Finset

namespace Probly

open Lean in
syntax (name := lift_lets) "lift_lets" (Parser.Tactic.config)? : conv

open Lean Meta Elab Tactic Mathlib.Tactic Lean.Elab.Tactic.Conv in
elab_rules : tactic
  | `(conv| lift_lets) => do -- $[$cfg:config]? $[$loc:location]?
    let lhs ← getLhs
    let lhs' ← lhs.liftLets mkLetFVars {}
    changeLhs lhs'


noncomputable
def test (θ : ℝ) : Rand ℝ :=
  let b ~ (flip θ)
  if b then
    Rand.pure 0
  else
    Rand.pure (-θ/2)



variable (θ : ℝ)


#check (randFwdDeriv test θ 1)
  rewrite_by
  unfold test
  simp (disch:=sorry) only [rand_simp]

theorem push_to_if {c} [Decidable c] (f : α → β) (a a' : α) :
    f (if c then a else a') = if c then f a else f a' := sorry

set_option trace.Meta.Tactic.simp.rewrite true in
#check (randFwdDeriv test θ 1).fdE id
  rewrite_by
  unfold test
  conv => 
    enter [1]
    simp (config := {zeta:=false}) (disch:=sorry) only [rand_simp]
  simp (config := {zeta:=false}) (disch:=sorry) [rand_simp]


variable (φ : ℝ → ℝ)

noncomputable
def _root_.Bool.toReal (b : Bool) : ℝ := if b then 1 else 0


noncomputable
def test2 (θ : ℝ) : Rand ℝ :=
  let b ~ (flip θ)
  if b then
    Rand.pure 0
  else
    let b' ~ (flip θ)
    if b' then
      Rand.pure (4*θ)
    else
      Rand.pure (-θ/2)

#check (deriv fun θ => (test2 θ).E φ)
  rewrite_by
  
  unfold deriv; simp (disch:=sorry) only [Rand.E.arg_x.fderiv_rule]

  unfold test2
  conv => 
    enter [θ,1,1]
    simp (config := {zeta:=false}) (disch:=sorry) only [rand_simp]

  conv => 
    enter [θ,1]
    simp (config := {zeta:=false}) (disch:=sorry) only [rand_simp]
    lift_lets
  simp

#exit
  -- conv => 
  --   enter [1]
  --   simp (config := {zeta:=false}) (disch:=sorry) only [rand_simp]
  -- lift_lets
  -- simp (config := {zeta:=false}) (disch:=sorry) [rand_simp]


#check (randFwdDeriv test2 θ 1).fdE φ
  rewrite_by
  unfold test2
  conv => 
    enter [1]
    simp (config := {zeta:=false}) (disch:=sorry) only [rand_simp]
  lift_lets
  simp (config := {zeta:=false}) (disch:=sorry) [rand_simp]



#check (test θ).pdf' .count
  rewrite_by
    unfold test
    simp [rand_simp,flip]
    enter[y]
