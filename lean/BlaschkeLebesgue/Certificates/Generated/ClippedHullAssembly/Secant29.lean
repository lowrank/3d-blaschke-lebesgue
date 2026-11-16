module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip29
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant29
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (464 + j) 512 = true :=
  Fin.cases SecantKernel.Strip29.bucket464 (Fin.cases SecantKernel.Strip29.bucket465 (Fin.cases SecantKernel.Strip29.bucket466 (Fin.cases SecantKernel.Strip29.bucket467 (Fin.cases SecantKernel.Strip29.bucket468 (Fin.cases SecantKernel.Strip29.bucket469 (Fin.cases SecantKernel.Strip29.bucket470 (Fin.cases SecantKernel.Strip29.bucket471 (Fin.cases SecantKernel.Strip29.bucket472 (Fin.cases SecantKernel.Strip29.bucket473 (Fin.cases SecantKernel.Strip29.bucket474 (Fin.cases SecantKernel.Strip29.bucket475 (Fin.cases SecantKernel.Strip29.bucket476 (Fin.cases SecantKernel.Strip29.bucket477 (Fin.cases SecantKernel.Strip29.bucket478 (Fin.cases SecantKernel.Strip29.bucket479 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant29
