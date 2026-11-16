module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip17
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant17
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (272 + j) 512 = true :=
  Fin.cases SecantKernel.Strip17.bucket272 (Fin.cases SecantKernel.Strip17.bucket273 (Fin.cases SecantKernel.Strip17.bucket274 (Fin.cases SecantKernel.Strip17.bucket275 (Fin.cases SecantKernel.Strip17.bucket276 (Fin.cases SecantKernel.Strip17.bucket277 (Fin.cases SecantKernel.Strip17.bucket278 (Fin.cases SecantKernel.Strip17.bucket279 (Fin.cases SecantKernel.Strip17.bucket280 (Fin.cases SecantKernel.Strip17.bucket281 (Fin.cases SecantKernel.Strip17.bucket282 (Fin.cases SecantKernel.Strip17.bucket283 (Fin.cases SecantKernel.Strip17.bucket284 (Fin.cases SecantKernel.Strip17.bucket285 (Fin.cases SecantKernel.Strip17.bucket286 (Fin.cases SecantKernel.Strip17.bucket287 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant17
