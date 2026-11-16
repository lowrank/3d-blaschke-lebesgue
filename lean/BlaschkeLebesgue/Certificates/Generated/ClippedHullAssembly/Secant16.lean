module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip16
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant16
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (256 + j) 512 = true :=
  Fin.cases SecantKernel.Strip16.bucket256 (Fin.cases SecantKernel.Strip16.bucket257 (Fin.cases SecantKernel.Strip16.bucket258 (Fin.cases SecantKernel.Strip16.bucket259 (Fin.cases SecantKernel.Strip16.bucket260 (Fin.cases SecantKernel.Strip16.bucket261 (Fin.cases SecantKernel.Strip16.bucket262 (Fin.cases SecantKernel.Strip16.bucket263 (Fin.cases SecantKernel.Strip16.bucket264 (Fin.cases SecantKernel.Strip16.bucket265 (Fin.cases SecantKernel.Strip16.bucket266 (Fin.cases SecantKernel.Strip16.bucket267 (Fin.cases SecantKernel.Strip16.bucket268 (Fin.cases SecantKernel.Strip16.bucket269 (Fin.cases SecantKernel.Strip16.bucket270 (Fin.cases SecantKernel.Strip16.bucket271 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant16
