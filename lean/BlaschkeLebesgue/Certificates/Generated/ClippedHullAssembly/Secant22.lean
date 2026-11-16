module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip22
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant22
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (352 + j) 512 = true :=
  Fin.cases SecantKernel.Strip22.bucket352 (Fin.cases SecantKernel.Strip22.bucket353 (Fin.cases SecantKernel.Strip22.bucket354 (Fin.cases SecantKernel.Strip22.bucket355 (Fin.cases SecantKernel.Strip22.bucket356 (Fin.cases SecantKernel.Strip22.bucket357 (Fin.cases SecantKernel.Strip22.bucket358 (Fin.cases SecantKernel.Strip22.bucket359 (Fin.cases SecantKernel.Strip22.bucket360 (Fin.cases SecantKernel.Strip22.bucket361 (Fin.cases SecantKernel.Strip22.bucket362 (Fin.cases SecantKernel.Strip22.bucket363 (Fin.cases SecantKernel.Strip22.bucket364 (Fin.cases SecantKernel.Strip22.bucket365 (Fin.cases SecantKernel.Strip22.bucket366 (Fin.cases SecantKernel.Strip22.bucket367 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant22
