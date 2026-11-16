module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip23
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant23
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (368 + j) 512 = true :=
  Fin.cases SecantKernel.Strip23.bucket368 (Fin.cases SecantKernel.Strip23.bucket369 (Fin.cases SecantKernel.Strip23.bucket370 (Fin.cases SecantKernel.Strip23.bucket371 (Fin.cases SecantKernel.Strip23.bucket372 (Fin.cases SecantKernel.Strip23.bucket373 (Fin.cases SecantKernel.Strip23.bucket374 (Fin.cases SecantKernel.Strip23.bucket375 (Fin.cases SecantKernel.Strip23.bucket376 (Fin.cases SecantKernel.Strip23.bucket377 (Fin.cases SecantKernel.Strip23.bucket378 (Fin.cases SecantKernel.Strip23.bucket379 (Fin.cases SecantKernel.Strip23.bucket380 (Fin.cases SecantKernel.Strip23.bucket381 (Fin.cases SecantKernel.Strip23.bucket382 (Fin.cases SecantKernel.Strip23.bucket383 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant23
