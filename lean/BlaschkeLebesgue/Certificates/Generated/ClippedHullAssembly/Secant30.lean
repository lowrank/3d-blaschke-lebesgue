module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip30
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant30
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (480 + j) 512 = true :=
  Fin.cases SecantKernel.Strip30.bucket480 (Fin.cases SecantKernel.Strip30.bucket481 (Fin.cases SecantKernel.Strip30.bucket482 (Fin.cases SecantKernel.Strip30.bucket483 (Fin.cases SecantKernel.Strip30.bucket484 (Fin.cases SecantKernel.Strip30.bucket485 (Fin.cases SecantKernel.Strip30.bucket486 (Fin.cases SecantKernel.Strip30.bucket487 (Fin.cases SecantKernel.Strip30.bucket488 (Fin.cases SecantKernel.Strip30.bucket489 (Fin.cases SecantKernel.Strip30.bucket490 (Fin.cases SecantKernel.Strip30.bucket491 (Fin.cases SecantKernel.Strip30.bucket492 (Fin.cases SecantKernel.Strip30.bucket493 (Fin.cases SecantKernel.Strip30.bucket494 (Fin.cases SecantKernel.Strip30.bucket495 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant30
