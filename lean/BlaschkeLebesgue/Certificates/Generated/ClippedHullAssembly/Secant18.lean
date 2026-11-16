module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip18
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant18
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (288 + j) 512 = true :=
  Fin.cases SecantKernel.Strip18.bucket288 (Fin.cases SecantKernel.Strip18.bucket289 (Fin.cases SecantKernel.Strip18.bucket290 (Fin.cases SecantKernel.Strip18.bucket291 (Fin.cases SecantKernel.Strip18.bucket292 (Fin.cases SecantKernel.Strip18.bucket293 (Fin.cases SecantKernel.Strip18.bucket294 (Fin.cases SecantKernel.Strip18.bucket295 (Fin.cases SecantKernel.Strip18.bucket296 (Fin.cases SecantKernel.Strip18.bucket297 (Fin.cases SecantKernel.Strip18.bucket298 (Fin.cases SecantKernel.Strip18.bucket299 (Fin.cases SecantKernel.Strip18.bucket300 (Fin.cases SecantKernel.Strip18.bucket301 (Fin.cases SecantKernel.Strip18.bucket302 (Fin.cases SecantKernel.Strip18.bucket303 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant18
