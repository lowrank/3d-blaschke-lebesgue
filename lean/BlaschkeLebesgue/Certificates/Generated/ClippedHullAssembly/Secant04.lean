module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip04
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant04
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (64 + j) 512 = true :=
  Fin.cases SecantKernel.Strip04.bucket064 (Fin.cases SecantKernel.Strip04.bucket065 (Fin.cases SecantKernel.Strip04.bucket066 (Fin.cases SecantKernel.Strip04.bucket067 (Fin.cases SecantKernel.Strip04.bucket068 (Fin.cases SecantKernel.Strip04.bucket069 (Fin.cases SecantKernel.Strip04.bucket070 (Fin.cases SecantKernel.Strip04.bucket071 (Fin.cases SecantKernel.Strip04.bucket072 (Fin.cases SecantKernel.Strip04.bucket073 (Fin.cases SecantKernel.Strip04.bucket074 (Fin.cases SecantKernel.Strip04.bucket075 (Fin.cases SecantKernel.Strip04.bucket076 (Fin.cases SecantKernel.Strip04.bucket077 (Fin.cases SecantKernel.Strip04.bucket078 (Fin.cases SecantKernel.Strip04.bucket079 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant04
