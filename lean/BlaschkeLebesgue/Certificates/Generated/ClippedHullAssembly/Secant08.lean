module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip08
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant08
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (128 + j) 512 = true :=
  Fin.cases SecantKernel.Strip08.bucket128 (Fin.cases SecantKernel.Strip08.bucket129 (Fin.cases SecantKernel.Strip08.bucket130 (Fin.cases SecantKernel.Strip08.bucket131 (Fin.cases SecantKernel.Strip08.bucket132 (Fin.cases SecantKernel.Strip08.bucket133 (Fin.cases SecantKernel.Strip08.bucket134 (Fin.cases SecantKernel.Strip08.bucket135 (Fin.cases SecantKernel.Strip08.bucket136 (Fin.cases SecantKernel.Strip08.bucket137 (Fin.cases SecantKernel.Strip08.bucket138 (Fin.cases SecantKernel.Strip08.bucket139 (Fin.cases SecantKernel.Strip08.bucket140 (Fin.cases SecantKernel.Strip08.bucket141 (Fin.cases SecantKernel.Strip08.bucket142 (Fin.cases SecantKernel.Strip08.bucket143 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant08
