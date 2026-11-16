module

public import BlaschkeLebesgue.Certificates.TrigProgramComputation

/-! # Executable clipped-hull formulas

The input environment contains `R` and `x = 1-e`. Shared intermediate values
are evaluated once. Every operation is interpreted by the proved interval and
jet evaluators; the real formula identities are proved in `ClippedHullExpressions`.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.ClippedHull

open FixedPoint

local instance exprAdd : Add Expr := ⟨Expr.add⟩
local instance exprSub : Sub Expr := ⟨Expr.sub⟩
local instance exprMul : Mul Expr := ⟨Expr.mul⟩
local instance exprDiv : Div Expr := ⟨fun a b ↦ .mul a (.inv b)⟩
local instance exprNat (n : ℕ) : OfNat Expr n := ⟨Expr.rational n⟩

local notation "X" => Expr.var
local notation "C" => Expr.rational
local notation "sq" => Expr.sq
local notation "rt" => Expr.sqrt

def inputEnv {α : Type*} (R x : α) : ℕ → α := pushEnv R (fun _ ↦ x)

/-- Final state: `F,phi,phiHalf,phiArg,gamma,gammaArg,theta,thetaArg,q,k,m,r,s,t,R,x`. -/
def baseProgram : TrigProgram := [
  .algebra (sq (X 0)), -- t
  .algebra (rt (X 2)), -- s
  .algebra (rt (1 - X 3 / 4)), -- r
  .algebra (rt (X 2 - X 4 / 4)), -- m
  .algebra (rt (1 - 1 / (4 * X 3))), -- k
  .algebra (rt (X 4 * (4 - X 6) - 1)), -- q
  .algebra (X 4 / 2), -- thetaArg
  .asin 0, -- theta
  .algebra (1 / (2 * X 8)), -- gammaArg
  .acos 0, -- gamma
  .algebra ((1 - X 11 / 2) / (2 * X 7 * X 6)), -- phiArg
  .acos 0, -- phiHalf
  .algebra (2 * X 0), -- phi
  .algebra (X 11 / 2 - sq (X 11) * X 11 / 24 - X 10 * X 5), -- F
]

/-- Final state: `combinedDx,innerDx,outerDx,F,phi,phiHalf,phiArg,gamma,gammaArg,theta,thetaArg,q,k,m,r,s,t,R,x`. -/
def dxTail : TrigProgram := [
  .algebra ((2 - X 15) * X 8 / (4 * X 12 * (4 * X 13 - X 15)) - (4 - X 15) * X 1 / (16 * X 12)), -- outerDx
  .algebra (X 2 * (C (-1/16) * X 13 + X 7 / (8 * X 12)) + (X 16 + 6 - 8 * X 15) * X 9 / (4 * X 13 * (4 * X 14 - X 16)) - (6 * X 14 - X 14 * X 16 - 2) * X 7 / (2 * X 12 * X 9 * (4 * X 14 - X 16)) - (2 * X 15 * X 10) * (1 - 2 * X 14) * X 5 / (X 13 * X 9 * (4 * X 14 - X 16))), -- innerDx
  .algebra ((47 * X 0 - X 1) / 46), -- combinedDx
]

/-- Final state: `baseline,innerBase,outerBase,pi,combined,inner,outer,b,z,T,Psi,PsiArg,V,VArg,U,UArg,F,phi,phiHalf,phiArg,gamma,gammaArg,theta,thetaArg,q,k,m,r,s,t,R,x`. -/
def volumeTail : TrigProgram := [
  .algebra (X 12 / (4 * X 14 * X 11 * X 9)), -- UArg
  .acos 0, -- U
  .algebra ((2 * sq (X 11) - X 17) / (2 * sq (X 11))), -- VArg
  .acos 0, -- V
  .algebra ((1 - 2 * X 17) * X 16 / (4 * X 18 * X 13 * X 14)), -- PsiArg
  .acos 0, -- Psi
  .algebra (X 18 * X 14), -- T
  .algebra (X 20 - X 21 - X 20 * X 21 / 3), -- z
  .algebra (C (1/2) - 3 / (8 * X 22) - X 17 * X 12 / 2 - X 0), -- b
  .algebra ((C (-4) * X 7 - 2 * X 22 * X 23 * X 5 + (C (-3) * X 21 / 2 + sq (X 21) * X 21 / 8) * X 10 + X 2 / 2 + (4 * X 22 * X 23 + 3 / (2 * X 23)) * X 3) / 3), -- outer
  .algebra (C (4/3) * X 8 - 2 * X 2 * X 6 + X 11 * X 10 - X 3 / 6 - 4 * X 1 * X 4), -- inner
  .algebra ((47 * X 0 - X 1) / 46), -- combined
  .pi, -- pi
  .algebra (8 * X 0 / 3 - X 0 / X 27), -- outerBase
  .algebra (8 * X 1 / 3 - 3 * X 1 / X 28 - 4 * X 1 * X 23 * X 18), -- innerBase
  .algebra ((47 * X 0 - X 1) / 46 + 6 * X 3), -- baseline
]

def dxProgram : TrigProgram := baseProgram ++ dxTail
def volumeProgram : TrigProgram := baseProgram ++ volumeTail

@[ext] structure Derivatives (α : Type*) where
  outer : α
  inner : α
  combined : α
  deriving DecidableEq, Inhabited

@[ext] structure Volumes (α : Type*) where
  outer : α
  inner : α
  combined : α
  baseline : α
  deriving DecidableEq, Inhabited

def dxOut {α : Type*} (env : ℕ → α) : Derivatives α := ⟨env 2, env 1, env 0⟩
def volumeOut {α : Type*} (env : ℕ → α) : Volumes α := ⟨env 6, env 5, env 4, env 0⟩

def dxInterval (p n : ℕ) (R x : Interval) : Option (Derivatives Interval) :=
  (TrigProgram.interval p n dxProgram (inputEnv R x)).map dxOut

def dxJet (p n : ℕ) (R x : Jet) : Option (Derivatives Jet) :=
  (TrigProgram.jet p n dxProgram (inputEnv R x)).map dxOut

def volumeInterval (p n : ℕ) (R x : Interval) : Option (Volumes Interval) :=
  (TrigProgram.interval p n volumeProgram (inputEnv R x)).map volumeOut

def volumeJet (p n : ℕ) (R x : Jet) : Option (Volumes Jet) :=
  (TrigProgram.jet p n volumeProgram (inputEnv R x)).map volumeOut

end BlaschkeLebesgue.Certificates.ClippedHull
