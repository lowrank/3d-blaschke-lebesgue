module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip10
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant10
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (160 + j) 512 = true :=
  Fin.cases SecantKernel.Strip10.bucket160 (Fin.cases SecantKernel.Strip10.bucket161 (Fin.cases SecantKernel.Strip10.bucket162 (Fin.cases SecantKernel.Strip10.bucket163 (Fin.cases SecantKernel.Strip10.bucket164 (Fin.cases SecantKernel.Strip10.bucket165 (Fin.cases SecantKernel.Strip10.bucket166 (Fin.cases SecantKernel.Strip10.bucket167 (Fin.cases SecantKernel.Strip10.bucket168 (Fin.cases SecantKernel.Strip10.bucket169 (Fin.cases SecantKernel.Strip10.bucket170 (Fin.cases SecantKernel.Strip10.bucket171 (Fin.cases SecantKernel.Strip10.bucket172 (Fin.cases SecantKernel.Strip10.bucket173 (Fin.cases SecantKernel.Strip10.bucket174 (Fin.cases SecantKernel.Strip10.bucket175 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant10
