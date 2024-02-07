import Mathlib.Analysis.Calculus.FDeriv.Basic



variable {K : Type*} [NontriviallyNormedField K]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F]


variable (K)

noncomputable
def fwdDeriv (f : E → F) (x dx : E) : F×F := (f x, fderiv K f x dx)
