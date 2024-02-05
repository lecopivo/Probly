import Probly.Flip

namespace Probly

noncomputable
def test (θ : ℝ) : Rand ℝ :=
  let b ~ (flip θ)
  if b then
    Rand.pure 0
  else
    Rand.pure (-θ/2)


variable (θ ; ℝ)
set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.rewrite true in
#check (randFwdDeriv test θ 1).dval.expectedValueChange id
  rewrite_by
  unfold test
  simp (disch:=sorry) only [rand_simp]
  simp [FDRand.bind, FDRand.dpure]
