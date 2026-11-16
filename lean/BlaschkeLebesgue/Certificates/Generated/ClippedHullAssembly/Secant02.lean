module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip02
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant02
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (32 + j) 512 = true :=
  Fin.cases SecantKernel.Strip02.bucket032 (Fin.cases SecantKernel.Strip02.bucket033 (Fin.cases SecantKernel.Strip02.bucket034 (Fin.cases SecantKernel.Strip02.bucket035 (Fin.cases SecantKernel.Strip02.bucket036 (Fin.cases SecantKernel.Strip02.bucket037 (Fin.cases SecantKernel.Strip02.bucket038 (Fin.cases SecantKernel.Strip02.bucket039 (Fin.cases SecantKernel.Strip02.bucket040 (Fin.cases SecantKernel.Strip02.bucket041 (Fin.cases SecantKernel.Strip02.bucket042 (Fin.cases SecantKernel.Strip02.bucket043 (Fin.cases SecantKernel.Strip02.bucket044 (Fin.cases SecantKernel.Strip02.bucket045 (Fin.cases SecantKernel.Strip02.bucket046 (Fin.cases SecantKernel.Strip02.bucket047 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant02
