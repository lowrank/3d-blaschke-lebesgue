module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip11
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant11
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (176 + j) 512 = true :=
  Fin.cases SecantKernel.Strip11.bucket176 (Fin.cases SecantKernel.Strip11.bucket177 (Fin.cases SecantKernel.Strip11.bucket178 (Fin.cases SecantKernel.Strip11.bucket179 (Fin.cases SecantKernel.Strip11.bucket180 (Fin.cases SecantKernel.Strip11.bucket181 (Fin.cases SecantKernel.Strip11.bucket182 (Fin.cases SecantKernel.Strip11.bucket183 (Fin.cases SecantKernel.Strip11.bucket184 (Fin.cases SecantKernel.Strip11.bucket185 (Fin.cases SecantKernel.Strip11.bucket186 (Fin.cases SecantKernel.Strip11.bucket187 (Fin.cases SecantKernel.Strip11.bucket188 (Fin.cases SecantKernel.Strip11.bucket189 (Fin.cases SecantKernel.Strip11.bucket190 (Fin.cases SecantKernel.Strip11.bucket191 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant11
