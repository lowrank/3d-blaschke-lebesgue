module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip28
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant28
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (448 + j) 512 = true :=
  Fin.cases SecantKernel.Strip28.bucket448 (Fin.cases SecantKernel.Strip28.bucket449 (Fin.cases SecantKernel.Strip28.bucket450 (Fin.cases SecantKernel.Strip28.bucket451 (Fin.cases SecantKernel.Strip28.bucket452 (Fin.cases SecantKernel.Strip28.bucket453 (Fin.cases SecantKernel.Strip28.bucket454 (Fin.cases SecantKernel.Strip28.bucket455 (Fin.cases SecantKernel.Strip28.bucket456 (Fin.cases SecantKernel.Strip28.bucket457 (Fin.cases SecantKernel.Strip28.bucket458 (Fin.cases SecantKernel.Strip28.bucket459 (Fin.cases SecantKernel.Strip28.bucket460 (Fin.cases SecantKernel.Strip28.bucket461 (Fin.cases SecantKernel.Strip28.bucket462 (Fin.cases SecantKernel.Strip28.bucket463 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant28
