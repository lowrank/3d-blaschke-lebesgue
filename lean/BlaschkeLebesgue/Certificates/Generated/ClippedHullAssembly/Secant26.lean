module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip26
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant26
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (416 + j) 512 = true :=
  Fin.cases SecantKernel.Strip26.bucket416 (Fin.cases SecantKernel.Strip26.bucket417 (Fin.cases SecantKernel.Strip26.bucket418 (Fin.cases SecantKernel.Strip26.bucket419 (Fin.cases SecantKernel.Strip26.bucket420 (Fin.cases SecantKernel.Strip26.bucket421 (Fin.cases SecantKernel.Strip26.bucket422 (Fin.cases SecantKernel.Strip26.bucket423 (Fin.cases SecantKernel.Strip26.bucket424 (Fin.cases SecantKernel.Strip26.bucket425 (Fin.cases SecantKernel.Strip26.bucket426 (Fin.cases SecantKernel.Strip26.bucket427 (Fin.cases SecantKernel.Strip26.bucket428 (Fin.cases SecantKernel.Strip26.bucket429 (Fin.cases SecantKernel.Strip26.bucket430 (Fin.cases SecantKernel.Strip26.bucket431 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant26
