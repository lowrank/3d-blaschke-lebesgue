module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip12
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant12
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (192 + j) 512 = true :=
  Fin.cases SecantKernel.Strip12.bucket192 (Fin.cases SecantKernel.Strip12.bucket193 (Fin.cases SecantKernel.Strip12.bucket194 (Fin.cases SecantKernel.Strip12.bucket195 (Fin.cases SecantKernel.Strip12.bucket196 (Fin.cases SecantKernel.Strip12.bucket197 (Fin.cases SecantKernel.Strip12.bucket198 (Fin.cases SecantKernel.Strip12.bucket199 (Fin.cases SecantKernel.Strip12.bucket200 (Fin.cases SecantKernel.Strip12.bucket201 (Fin.cases SecantKernel.Strip12.bucket202 (Fin.cases SecantKernel.Strip12.bucket203 (Fin.cases SecantKernel.Strip12.bucket204 (Fin.cases SecantKernel.Strip12.bucket205 (Fin.cases SecantKernel.Strip12.bucket206 (Fin.cases SecantKernel.Strip12.bucket207 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant12
