module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip05
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant05
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (80 + j) 512 = true :=
  Fin.cases SecantKernel.Strip05.bucket080 (Fin.cases SecantKernel.Strip05.bucket081 (Fin.cases SecantKernel.Strip05.bucket082 (Fin.cases SecantKernel.Strip05.bucket083 (Fin.cases SecantKernel.Strip05.bucket084 (Fin.cases SecantKernel.Strip05.bucket085 (Fin.cases SecantKernel.Strip05.bucket086 (Fin.cases SecantKernel.Strip05.bucket087 (Fin.cases SecantKernel.Strip05.bucket088 (Fin.cases SecantKernel.Strip05.bucket089 (Fin.cases SecantKernel.Strip05.bucket090 (Fin.cases SecantKernel.Strip05.bucket091 (Fin.cases SecantKernel.Strip05.bucket092 (Fin.cases SecantKernel.Strip05.bucket093 (Fin.cases SecantKernel.Strip05.bucket094 (Fin.cases SecantKernel.Strip05.bucket095 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant05
