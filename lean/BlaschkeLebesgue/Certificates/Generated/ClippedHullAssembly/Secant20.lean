module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip20
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant20
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (320 + j) 512 = true :=
  Fin.cases SecantKernel.Strip20.bucket320 (Fin.cases SecantKernel.Strip20.bucket321 (Fin.cases SecantKernel.Strip20.bucket322 (Fin.cases SecantKernel.Strip20.bucket323 (Fin.cases SecantKernel.Strip20.bucket324 (Fin.cases SecantKernel.Strip20.bucket325 (Fin.cases SecantKernel.Strip20.bucket326 (Fin.cases SecantKernel.Strip20.bucket327 (Fin.cases SecantKernel.Strip20.bucket328 (Fin.cases SecantKernel.Strip20.bucket329 (Fin.cases SecantKernel.Strip20.bucket330 (Fin.cases SecantKernel.Strip20.bucket331 (Fin.cases SecantKernel.Strip20.bucket332 (Fin.cases SecantKernel.Strip20.bucket333 (Fin.cases SecantKernel.Strip20.bucket334 (Fin.cases SecantKernel.Strip20.bucket335 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant20
