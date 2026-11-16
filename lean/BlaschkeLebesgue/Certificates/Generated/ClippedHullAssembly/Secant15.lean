module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip15
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant15
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (240 + j) 512 = true :=
  Fin.cases SecantKernel.Strip15.bucket240 (Fin.cases SecantKernel.Strip15.bucket241 (Fin.cases SecantKernel.Strip15.bucket242 (Fin.cases SecantKernel.Strip15.bucket243 (Fin.cases SecantKernel.Strip15.bucket244 (Fin.cases SecantKernel.Strip15.bucket245 (Fin.cases SecantKernel.Strip15.bucket246 (Fin.cases SecantKernel.Strip15.bucket247 (Fin.cases SecantKernel.Strip15.bucket248 (Fin.cases SecantKernel.Strip15.bucket249 (Fin.cases SecantKernel.Strip15.bucket250 (Fin.cases SecantKernel.Strip15.bucket251 (Fin.cases SecantKernel.Strip15.bucket252 (Fin.cases SecantKernel.Strip15.bucket253 (Fin.cases SecantKernel.Strip15.bucket254 (Fin.cases SecantKernel.Strip15.bucket255 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant15
