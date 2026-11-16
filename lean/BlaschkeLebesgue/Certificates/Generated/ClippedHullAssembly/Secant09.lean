module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip09
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant09
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (144 + j) 512 = true :=
  Fin.cases SecantKernel.Strip09.bucket144 (Fin.cases SecantKernel.Strip09.bucket145 (Fin.cases SecantKernel.Strip09.bucket146 (Fin.cases SecantKernel.Strip09.bucket147 (Fin.cases SecantKernel.Strip09.bucket148 (Fin.cases SecantKernel.Strip09.bucket149 (Fin.cases SecantKernel.Strip09.bucket150 (Fin.cases SecantKernel.Strip09.bucket151 (Fin.cases SecantKernel.Strip09.bucket152 (Fin.cases SecantKernel.Strip09.bucket153 (Fin.cases SecantKernel.Strip09.bucket154 (Fin.cases SecantKernel.Strip09.bucket155 (Fin.cases SecantKernel.Strip09.bucket156 (Fin.cases SecantKernel.Strip09.bucket157 (Fin.cases SecantKernel.Strip09.bucket158 (Fin.cases SecantKernel.Strip09.bucket159 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant09
