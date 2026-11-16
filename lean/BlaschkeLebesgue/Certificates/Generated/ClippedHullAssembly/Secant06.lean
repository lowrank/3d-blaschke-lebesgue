module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip06
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant06
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (96 + j) 512 = true :=
  Fin.cases SecantKernel.Strip06.bucket096 (Fin.cases SecantKernel.Strip06.bucket097 (Fin.cases SecantKernel.Strip06.bucket098 (Fin.cases SecantKernel.Strip06.bucket099 (Fin.cases SecantKernel.Strip06.bucket100 (Fin.cases SecantKernel.Strip06.bucket101 (Fin.cases SecantKernel.Strip06.bucket102 (Fin.cases SecantKernel.Strip06.bucket103 (Fin.cases SecantKernel.Strip06.bucket104 (Fin.cases SecantKernel.Strip06.bucket105 (Fin.cases SecantKernel.Strip06.bucket106 (Fin.cases SecantKernel.Strip06.bucket107 (Fin.cases SecantKernel.Strip06.bucket108 (Fin.cases SecantKernel.Strip06.bucket109 (Fin.cases SecantKernel.Strip06.bucket110 (Fin.cases SecantKernel.Strip06.bucket111 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant06
