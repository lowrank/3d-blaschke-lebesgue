module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip14
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant14
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (224 + j) 512 = true :=
  Fin.cases SecantKernel.Strip14.bucket224 (Fin.cases SecantKernel.Strip14.bucket225 (Fin.cases SecantKernel.Strip14.bucket226 (Fin.cases SecantKernel.Strip14.bucket227 (Fin.cases SecantKernel.Strip14.bucket228 (Fin.cases SecantKernel.Strip14.bucket229 (Fin.cases SecantKernel.Strip14.bucket230 (Fin.cases SecantKernel.Strip14.bucket231 (Fin.cases SecantKernel.Strip14.bucket232 (Fin.cases SecantKernel.Strip14.bucket233 (Fin.cases SecantKernel.Strip14.bucket234 (Fin.cases SecantKernel.Strip14.bucket235 (Fin.cases SecantKernel.Strip14.bucket236 (Fin.cases SecantKernel.Strip14.bucket237 (Fin.cases SecantKernel.Strip14.bucket238 (Fin.cases SecantKernel.Strip14.bucket239 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant14
