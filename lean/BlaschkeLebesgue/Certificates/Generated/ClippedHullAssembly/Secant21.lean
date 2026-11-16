module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip21
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant21
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (336 + j) 512 = true :=
  Fin.cases SecantKernel.Strip21.bucket336 (Fin.cases SecantKernel.Strip21.bucket337 (Fin.cases SecantKernel.Strip21.bucket338 (Fin.cases SecantKernel.Strip21.bucket339 (Fin.cases SecantKernel.Strip21.bucket340 (Fin.cases SecantKernel.Strip21.bucket341 (Fin.cases SecantKernel.Strip21.bucket342 (Fin.cases SecantKernel.Strip21.bucket343 (Fin.cases SecantKernel.Strip21.bucket344 (Fin.cases SecantKernel.Strip21.bucket345 (Fin.cases SecantKernel.Strip21.bucket346 (Fin.cases SecantKernel.Strip21.bucket347 (Fin.cases SecantKernel.Strip21.bucket348 (Fin.cases SecantKernel.Strip21.bucket349 (Fin.cases SecantKernel.Strip21.bucket350 (Fin.cases SecantKernel.Strip21.bucket351 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant21
