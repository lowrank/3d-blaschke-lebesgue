module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip19
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant19
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (304 + j) 512 = true :=
  Fin.cases SecantKernel.Strip19.bucket304 (Fin.cases SecantKernel.Strip19.bucket305 (Fin.cases SecantKernel.Strip19.bucket306 (Fin.cases SecantKernel.Strip19.bucket307 (Fin.cases SecantKernel.Strip19.bucket308 (Fin.cases SecantKernel.Strip19.bucket309 (Fin.cases SecantKernel.Strip19.bucket310 (Fin.cases SecantKernel.Strip19.bucket311 (Fin.cases SecantKernel.Strip19.bucket312 (Fin.cases SecantKernel.Strip19.bucket313 (Fin.cases SecantKernel.Strip19.bucket314 (Fin.cases SecantKernel.Strip19.bucket315 (Fin.cases SecantKernel.Strip19.bucket316 (Fin.cases SecantKernel.Strip19.bucket317 (Fin.cases SecantKernel.Strip19.bucket318 (Fin.cases SecantKernel.Strip19.bucket319 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant19
