module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip27
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant27
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (432 + j) 512 = true :=
  Fin.cases SecantKernel.Strip27.bucket432 (Fin.cases SecantKernel.Strip27.bucket433 (Fin.cases SecantKernel.Strip27.bucket434 (Fin.cases SecantKernel.Strip27.bucket435 (Fin.cases SecantKernel.Strip27.bucket436 (Fin.cases SecantKernel.Strip27.bucket437 (Fin.cases SecantKernel.Strip27.bucket438 (Fin.cases SecantKernel.Strip27.bucket439 (Fin.cases SecantKernel.Strip27.bucket440 (Fin.cases SecantKernel.Strip27.bucket441 (Fin.cases SecantKernel.Strip27.bucket442 (Fin.cases SecantKernel.Strip27.bucket443 (Fin.cases SecantKernel.Strip27.bucket444 (Fin.cases SecantKernel.Strip27.bucket445 (Fin.cases SecantKernel.Strip27.bucket446 (Fin.cases SecantKernel.Strip27.bucket447 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant27
