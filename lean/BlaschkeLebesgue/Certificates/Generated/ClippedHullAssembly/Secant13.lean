module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip13
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant13
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (208 + j) 512 = true :=
  Fin.cases SecantKernel.Strip13.bucket208 (Fin.cases SecantKernel.Strip13.bucket209 (Fin.cases SecantKernel.Strip13.bucket210 (Fin.cases SecantKernel.Strip13.bucket211 (Fin.cases SecantKernel.Strip13.bucket212 (Fin.cases SecantKernel.Strip13.bucket213 (Fin.cases SecantKernel.Strip13.bucket214 (Fin.cases SecantKernel.Strip13.bucket215 (Fin.cases SecantKernel.Strip13.bucket216 (Fin.cases SecantKernel.Strip13.bucket217 (Fin.cases SecantKernel.Strip13.bucket218 (Fin.cases SecantKernel.Strip13.bucket219 (Fin.cases SecantKernel.Strip13.bucket220 (Fin.cases SecantKernel.Strip13.bucket221 (Fin.cases SecantKernel.Strip13.bucket222 (Fin.cases SecantKernel.Strip13.bucket223 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant13
