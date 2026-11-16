module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip25
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant25
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (400 + j) 512 = true :=
  Fin.cases SecantKernel.Strip25.bucket400 (Fin.cases SecantKernel.Strip25.bucket401 (Fin.cases SecantKernel.Strip25.bucket402 (Fin.cases SecantKernel.Strip25.bucket403 (Fin.cases SecantKernel.Strip25.bucket404 (Fin.cases SecantKernel.Strip25.bucket405 (Fin.cases SecantKernel.Strip25.bucket406 (Fin.cases SecantKernel.Strip25.bucket407 (Fin.cases SecantKernel.Strip25.bucket408 (Fin.cases SecantKernel.Strip25.bucket409 (Fin.cases SecantKernel.Strip25.bucket410 (Fin.cases SecantKernel.Strip25.bucket411 (Fin.cases SecantKernel.Strip25.bucket412 (Fin.cases SecantKernel.Strip25.bucket413 (Fin.cases SecantKernel.Strip25.bucket414 (Fin.cases SecantKernel.Strip25.bucket415 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant25
