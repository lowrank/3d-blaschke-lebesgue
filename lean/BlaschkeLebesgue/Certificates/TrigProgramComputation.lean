module

public import BlaschkeLebesgue.Certificates.ExpressionComputation
public import BlaschkeLebesgue.Certificates.InverseTrigComputation

/-! # Executable programs with inverse-trigonometric instructions -/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.FixedPoint

inductive TrigOp where
  | algebra (e : Expr)
  | pi
  | atan (index : ℕ)
  | asin (index : ℕ)
  | acos (index : ℕ)
  deriving DecidableEq, Inhabited

namespace TrigOp

def interval (p n : ℕ) (e : TrigOp) (env : ℕ → Interval) : Option Interval := match e with
  | .algebra a => a.interval p env
  | .pi => Interval.pi p n
  | .atan i => Interval.checkedAtan p n (env i)
  | .asin i => Interval.asin p n (env i)
  | .acos i => Interval.acos p n (env i)

def jet (p n : ℕ) (e : TrigOp) (env : ℕ → Jet) : Option Jet := match e with
  | .algebra a => a.jet p env
  | .pi => (Interval.pi p n).map (Jet.const p)
  | .atan i => Jet.atan p n (env i)
  | .asin i => Jet.asin p n (env i)
  | .acos i => Jet.acos p n (env i)

end TrigOp

abbrev TrigProgram := List TrigOp

namespace TrigProgram

def interval (p n : ℕ) : TrigProgram → (ℕ → Interval) → Option (ℕ → Interval)
  | [], env => some env
  | e :: es, env => (e.interval p n env).bind fun v ↦ interval p n es (pushEnv v env)

def jet (p n : ℕ) : TrigProgram → (ℕ → Jet) → Option (ℕ → Jet)
  | [], env => some env
  | e :: es, env => (e.jet p n env).bind fun v ↦ jet p n es (pushEnv v env)

end TrigProgram
end BlaschkeLebesgue.Certificates.FixedPoint
