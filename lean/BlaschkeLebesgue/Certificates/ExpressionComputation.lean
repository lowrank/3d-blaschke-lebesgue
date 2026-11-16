module

public import BlaschkeLebesgue.Certificates.FixedPointComputation

/-!
# Executable projective expression programs

The interval and jet interpreters, formula programs, and output records share
no dependency on the analytic soundness proofs or on real-valued geometry.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.FixedPoint

def pushEnv {α : Type*} (x : α) (env : ℕ → α) : ℕ → α
  | 0 => x
  | n + 1 => env n

inductive Expr where
  | rational (q : ℚ)
  | var (index : ℕ)
  | neg (a : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | sq (a : Expr)
  | inv (a : Expr)
  | sqrt (a : Expr)
  | bind (value body : Expr)
  deriving DecidableEq, Inhabited

namespace Expr

def interval (p : ℕ) (e : Expr) (env : ℕ → Interval) : Option Interval := match e with
  | .rational q => some (Interval.rational p q.num q.den)
  | .var i => some (env i)
  | .neg a => (interval p a env).map Interval.neg
  | .add a b => (interval p a env).bind fun x ↦ (interval p b env).map (Interval.add x)
  | .sub a b => (interval p a env).bind fun x ↦ (interval p b env).map (Interval.sub x)
  | .mul a b => (interval p a env).bind fun x ↦ (interval p b env).map (Interval.mul p x)
  | .sq a => (interval p a env).map (Interval.sq p)
  | .inv a => (interval p a env).bind fun x ↦ if x.invCheck then some (Interval.inv p x) else none
  | .sqrt a => (interval p a env).bind fun x ↦ if x.sqrtCheck then some (Interval.sqrt p x) else none
  | .bind a b => (interval p a env).bind fun x ↦ interval p b (pushEnv x env)

def jet (p : ℕ) (e : Expr) (env : ℕ → Jet) : Option Jet := match e with
  | .rational q => some (Jet.const p (Interval.rational p q.num q.den))
  | .var i => some (env i)
  | .neg a => (jet p a env).map Jet.neg
  | .add a b => (jet p a env).bind fun x ↦ (jet p b env).map (Jet.add x)
  | .sub a b => (jet p a env).bind fun x ↦ (jet p b env).map (Jet.sub x)
  | .mul a b => (jet p a env).bind fun x ↦ (jet p b env).map (Jet.mul p x)
  | .sq a => (jet p a env).map (Jet.sq p)
  | .inv a => (jet p a env).bind fun x ↦ if x.v.invCheck then some (Jet.inv p x) else none
  | .sqrt a => (jet p a env).bind fun x ↦ if Jet.sqrtCheck p x then some (Jet.sqrt p x) else none
  | .bind a b => (jet p a env).bind fun x ↦ jet p b (pushEnv x env)

end Expr

abbrev Program := List Expr

namespace Program

def interval (p : ℕ) : Program → (ℕ → Interval) → Option (ℕ → Interval)
  | [], env => some env
  | e :: es, env => (e.interval p env).bind fun v ↦ interval p es (pushEnv v env)

def jet (p : ℕ) : Program → (ℕ → Jet) → Option (ℕ → Jet)
  | [], env => some env
  | e :: es, env => (e.jet p env).bind fun v ↦ jet p es (pushEnv v env)

end Program

end BlaschkeLebesgue.Certificates.FixedPoint

namespace BlaschkeLebesgue.Certificates.ProjectiveExpressions

open FixedPoint

local instance exprAdd : Add Expr := ⟨Expr.add⟩
local instance exprSub : Sub Expr := ⟨Expr.sub⟩
local instance exprMul : Mul Expr := ⟨Expr.mul⟩
local instance exprDiv : Div Expr := ⟨fun a b ↦ .mul a (.inv b)⟩
local instance exprNat (n : ℕ) : OfNat Expr n := ⟨Expr.rational n⟩

abbrev X := Expr.var
abbrev C := Expr.rational
abbrev sq := Expr.sq
abbrev rt := Expr.sqrt

@[ext] structure Params (α : Type*) where
  ra : α
  w : α
  c : α
  T : α
  deriving DecidableEq, Inhabited

@[ext] structure Values (α : Type*) where
  G : α
  D : α
  V : α
  deriving DecidableEq, Inhabited

def Params.map {α β : Type*} (f : α → β) (v : Params α) : Params β :=
  ⟨f v.ra, f v.w, f v.c, f v.T⟩

def Values.map {α β : Type*} (f : α → β) (v : Values α) : Values β :=
  ⟨f v.G, f v.D, f v.V⟩

def parameterEnv {α : Type*} (a b : α) : ℕ → α := pushEnv a (fun _ ↦ b)

def integrandEnv {α : Type*} (p : Params α) (s t : α) : ℕ → α :=
  pushEnv p.ra (pushEnv p.w (pushEnv p.c (pushEnv p.T (pushEnv s (fun _ ↦ t)))))

def paramsOut {α : Type*} (env : ℕ → α) : Params α := ⟨env 1, env 0, env 7, env 2⟩
def valuesOut {α : Type*} (env : ℕ → α) : Values α := ⟨env 3, env 2, env 0⟩

/-- Comments list the new intermediate; indices refer to the preceding state. -/
def parameterProgram : Program := [
  X 0 + X 1, -- A; state [A,a,b]
  X 2 / (2 * (1 - X 1)), -- c; state [c,A,a,b]
  X 3 / (4 * rt (1 - X 2) * rt (1 - sq (X 0)) * rt (C (1/8) - X 1 / 16)), -- eta
  rt (4 / (3 * (2 - X 2))), -- cb; state [cb,eta,c,A,a,b]
  rt (1 - sq (X 0)), -- sb; state [sb,cb,eta,c,A,a,b]
  rt (1 - sq (X 2)), -- ee; state [ee,sb,cb,eta,c,A,a,b]
  (X 1 * X 0 - X 2 * X 3) / (X 2 * X 0 + X 1 * X 3), -- T
  rt (C (3/4) + X 7 / 4), -- ra; state [ra,T,ee,sb,cb,eta,c,A,a,b]
  rt (C (1/2) + (X 8 - X 9) / 4) -- w
]

/-- Initial state: `[ra,w,c,T,s,t]`; final outputs are `G=3,D=2,V=0`. -/
def integrandProgram : Program := [
  X 3 * X 4, -- x
  X 0 * X 6, -- y
  sq (X 1), -- xx
  sq (X 1), -- yy
  1 + (X 1 + X 0) / (1 - sq (X 6)), -- W
  rt (X 0), -- rw
  rt (C (3/4)) * rt (1 + X 3) + X 6 * rt (1 + X 2) - X 7, -- N
  X 0 / X 1 - 1, -- G
  1 - X 8 * X 2 / rt (1 + X 4), -- D
  C (47/32) * X 0 - 2 * sq (X 0), -- q(D)
  8 * sq (X 13) * X 14 * X 2 * X 0 / (X 5 * X 4) -- V
]

def paramsInterval (p : ℕ) (a b : Interval) : Option (Params Interval) :=
  (Program.interval p parameterProgram (parameterEnv a b)).map paramsOut

def paramsJet (p : ℕ) (a b : Jet) : Option (Params Jet) :=
  (Program.jet p parameterProgram (parameterEnv a b)).map paramsOut

def valuesInterval (p : ℕ) (par : Params Interval) (s t : Interval) : Option (Values Interval) :=
  (Program.interval p integrandProgram (integrandEnv par s t)).map valuesOut

def valuesJet (p : ℕ) (par : Params Jet) (s t : Jet) : Option (Values Jet) :=
  (Program.jet p integrandProgram (integrandEnv par s t)).map valuesOut

def inputA (p : ℕ) (dir : Bool) (a : Interval) : Jet := if dir then Jet.var p a else Jet.const p a
def inputB (p : ℕ) (dir : Bool) (b : Interval) : Jet := if dir then Jet.const p b else Jet.var p b

def parameterJets (p : ℕ) (dir : Bool) (a b : Interval) : Option (Params Jet) :=
  paramsJet p (inputA p dir a) (inputB p dir b)

end BlaschkeLebesgue.Certificates.ProjectiveExpressions
