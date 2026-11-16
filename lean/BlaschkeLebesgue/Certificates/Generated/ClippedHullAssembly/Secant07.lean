module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip07
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant07
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (112 + j) 512 = true :=
  Fin.cases SecantKernel.Strip07.bucket112 (Fin.cases SecantKernel.Strip07.bucket113 (Fin.cases SecantKernel.Strip07.bucket114 (Fin.cases SecantKernel.Strip07.bucket115 (Fin.cases SecantKernel.Strip07.bucket116 (Fin.cases SecantKernel.Strip07.bucket117 (Fin.cases SecantKernel.Strip07.bucket118 (Fin.cases SecantKernel.Strip07.bucket119 (Fin.cases SecantKernel.Strip07.bucket120 (Fin.cases SecantKernel.Strip07.bucket121 (Fin.cases SecantKernel.Strip07.bucket122 (Fin.cases SecantKernel.Strip07.bucket123 (Fin.cases SecantKernel.Strip07.bucket124 (Fin.cases SecantKernel.Strip07.bucket125 (Fin.cases SecantKernel.Strip07.bucket126 (Fin.cases SecantKernel.Strip07.bucket127 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant07
