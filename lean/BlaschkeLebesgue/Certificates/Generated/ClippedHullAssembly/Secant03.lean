module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip03
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant03
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (48 + j) 512 = true :=
  Fin.cases SecantKernel.Strip03.bucket048 (Fin.cases SecantKernel.Strip03.bucket049 (Fin.cases SecantKernel.Strip03.bucket050 (Fin.cases SecantKernel.Strip03.bucket051 (Fin.cases SecantKernel.Strip03.bucket052 (Fin.cases SecantKernel.Strip03.bucket053 (Fin.cases SecantKernel.Strip03.bucket054 (Fin.cases SecantKernel.Strip03.bucket055 (Fin.cases SecantKernel.Strip03.bucket056 (Fin.cases SecantKernel.Strip03.bucket057 (Fin.cases SecantKernel.Strip03.bucket058 (Fin.cases SecantKernel.Strip03.bucket059 (Fin.cases SecantKernel.Strip03.bucket060 (Fin.cases SecantKernel.Strip03.bucket061 (Fin.cases SecantKernel.Strip03.bucket062 (Fin.cases SecantKernel.Strip03.bucket063 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant03
