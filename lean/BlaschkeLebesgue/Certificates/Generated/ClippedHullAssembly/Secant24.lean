module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip24
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant24
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (384 + j) 512 = true :=
  Fin.cases SecantKernel.Strip24.bucket384 (Fin.cases SecantKernel.Strip24.bucket385 (Fin.cases SecantKernel.Strip24.bucket386 (Fin.cases SecantKernel.Strip24.bucket387 (Fin.cases SecantKernel.Strip24.bucket388 (Fin.cases SecantKernel.Strip24.bucket389 (Fin.cases SecantKernel.Strip24.bucket390 (Fin.cases SecantKernel.Strip24.bucket391 (Fin.cases SecantKernel.Strip24.bucket392 (Fin.cases SecantKernel.Strip24.bucket393 (Fin.cases SecantKernel.Strip24.bucket394 (Fin.cases SecantKernel.Strip24.bucket395 (Fin.cases SecantKernel.Strip24.bucket396 (Fin.cases SecantKernel.Strip24.bucket397 (Fin.cases SecantKernel.Strip24.bucket398 (Fin.cases SecantKernel.Strip24.bucket399 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant24
