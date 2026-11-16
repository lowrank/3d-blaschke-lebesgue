module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip31
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant31
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (496 + j) 512 = true :=
  Fin.cases SecantKernel.Strip31.bucket496 (Fin.cases SecantKernel.Strip31.bucket497 (Fin.cases SecantKernel.Strip31.bucket498 (Fin.cases SecantKernel.Strip31.bucket499 (Fin.cases SecantKernel.Strip31.bucket500 (Fin.cases SecantKernel.Strip31.bucket501 (Fin.cases SecantKernel.Strip31.bucket502 (Fin.cases SecantKernel.Strip31.bucket503 (Fin.cases SecantKernel.Strip31.bucket504 (Fin.cases SecantKernel.Strip31.bucket505 (Fin.cases SecantKernel.Strip31.bucket506 (Fin.cases SecantKernel.Strip31.bucket507 (Fin.cases SecantKernel.Strip31.bucket508 (Fin.cases SecantKernel.Strip31.bucket509 (Fin.cases SecantKernel.Strip31.bucket510 (Fin.cases SecantKernel.Strip31.bucket511 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant31
