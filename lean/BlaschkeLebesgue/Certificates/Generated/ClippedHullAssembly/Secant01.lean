module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip01
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant01
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : ∀ j : Fin 16, secantCheck 128 64 (16 + j) 512 = true :=
  Fin.cases SecantKernel.Strip01.bucket016 (Fin.cases SecantKernel.Strip01.bucket017 (Fin.cases SecantKernel.Strip01.bucket018 (Fin.cases SecantKernel.Strip01.bucket019 (Fin.cases SecantKernel.Strip01.bucket020 (Fin.cases SecantKernel.Strip01.bucket021 (Fin.cases SecantKernel.Strip01.bucket022 (Fin.cases SecantKernel.Strip01.bucket023 (Fin.cases SecantKernel.Strip01.bucket024 (Fin.cases SecantKernel.Strip01.bucket025 (Fin.cases SecantKernel.Strip01.bucket026 (Fin.cases SecantKernel.Strip01.bucket027 (Fin.cases SecantKernel.Strip01.bucket028 (Fin.cases SecantKernel.Strip01.bucket029 (Fin.cases SecantKernel.Strip01.bucket030 (Fin.cases SecantKernel.Strip01.bucket031 (fun j ↦ Fin.elim0 j))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull.Assembly.Secant01
