module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip00
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant00
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (0 + j) 512 = true :=
  Fin.cases SecantKernel.Strip00.bucket000 (Fin.cases SecantKernel.Strip00.bucket001 (Fin.cases SecantKernel.Strip00.bucket002 (Fin.cases SecantKernel.Strip00.bucket003 (Fin.cases SecantKernel.Strip00.bucket004 (Fin.cases SecantKernel.Strip00.bucket005 (Fin.cases SecantKernel.Strip00.bucket006 (Fin.cases SecantKernel.Strip00.bucket007 (Fin.cases SecantKernel.Strip00.bucket008 (Fin.cases SecantKernel.Strip00.bucket009 (Fin.cases SecantKernel.Strip00.bucket010 (Fin.cases SecantKernel.Strip00.bucket011 (Fin.cases SecantKernel.Strip00.bucket012 (Fin.cases SecantKernel.Strip00.bucket013 (Fin.cases SecantKernel.Strip00.bucket014 (Fin.cases SecantKernel.Strip00.bucket015 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant00
