module
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign00
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign01
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign02
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign03
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign04
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign05
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign06
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign07
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign08
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign09
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign10
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign11
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign12
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign13
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign14
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign15
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign16
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign17
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign18
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign19
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign20
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign21
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign22
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign23
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign24
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign25
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign26
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign27
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign28
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign29
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign30
public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign31
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem all_edge_checks : ∀ i : Fin 32, ∀ j : Fin 100, edgeSignCheck 128 64 i j 32 100 = true :=
  Fin.cases Assembly.Sign00.verified (Fin.cases Assembly.Sign01.verified (Fin.cases Assembly.Sign02.verified (Fin.cases Assembly.Sign03.verified (Fin.cases Assembly.Sign04.verified (Fin.cases Assembly.Sign05.verified (Fin.cases Assembly.Sign06.verified (Fin.cases Assembly.Sign07.verified (Fin.cases Assembly.Sign08.verified (Fin.cases Assembly.Sign09.verified (Fin.cases Assembly.Sign10.verified (Fin.cases Assembly.Sign11.verified (Fin.cases Assembly.Sign12.verified (Fin.cases Assembly.Sign13.verified (Fin.cases Assembly.Sign14.verified (Fin.cases Assembly.Sign15.verified (Fin.cases Assembly.Sign16.verified (Fin.cases Assembly.Sign17.verified (Fin.cases Assembly.Sign18.verified (Fin.cases Assembly.Sign19.verified (Fin.cases Assembly.Sign20.verified (Fin.cases Assembly.Sign21.verified (Fin.cases Assembly.Sign22.verified (Fin.cases Assembly.Sign23.verified (Fin.cases Assembly.Sign24.verified (Fin.cases Assembly.Sign25.verified (Fin.cases Assembly.Sign26.verified (Fin.cases Assembly.Sign27.verified (Fin.cases Assembly.Sign28.verified (Fin.cases Assembly.Sign29.verified (Fin.cases Assembly.Sign30.verified (Fin.cases Assembly.Sign31.verified (fun j ↦ Fin.elim0 j))))))))))))))))))))))))))))))))
theorem all_baseline_checks : ∀ i : Fin 32, baselineSignCheck 128 64 i 32 = true :=
  Fin.cases Kernel.Strip00.baseline (Fin.cases Kernel.Strip01.baseline (Fin.cases Kernel.Strip02.baseline (Fin.cases Kernel.Strip03.baseline (Fin.cases Kernel.Strip04.baseline (Fin.cases Kernel.Strip05.baseline (Fin.cases Kernel.Strip06.baseline (Fin.cases Kernel.Strip07.baseline (Fin.cases Kernel.Strip08.baseline (Fin.cases Kernel.Strip09.baseline (Fin.cases Kernel.Strip10.baseline (Fin.cases Kernel.Strip11.baseline (Fin.cases Kernel.Strip12.baseline (Fin.cases Kernel.Strip13.baseline (Fin.cases Kernel.Strip14.baseline (Fin.cases Kernel.Strip15.baseline (Fin.cases Kernel.Strip16.baseline (Fin.cases Kernel.Strip17.baseline (Fin.cases Kernel.Strip18.baseline (Fin.cases Kernel.Strip19.baseline (Fin.cases Kernel.Strip20.baseline (Fin.cases Kernel.Strip21.baseline (Fin.cases Kernel.Strip22.baseline (Fin.cases Kernel.Strip23.baseline (Fin.cases Kernel.Strip24.baseline (Fin.cases Kernel.Strip25.baseline (Fin.cases Kernel.Strip26.baseline (Fin.cases Kernel.Strip27.baseline (Fin.cases Kernel.Strip28.baseline (Fin.cases Kernel.Strip29.baseline (Fin.cases Kernel.Strip30.baseline (Fin.cases Kernel.Strip31.baseline (fun j ↦ Fin.elim0 j))))))))))))))))))))))))))))))))
end BlaschkeLebesgue.Certificates.ClippedHull
