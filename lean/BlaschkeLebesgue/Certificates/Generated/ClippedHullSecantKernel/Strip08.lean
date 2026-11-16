module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 128 through 143 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip08

theorem bucket128 : secantCheck 128 64 128 512 = true := by decide +kernel
theorem bucket129 : secantCheck 128 64 129 512 = true := by decide +kernel
theorem bucket130 : secantCheck 128 64 130 512 = true := by decide +kernel
theorem bucket131 : secantCheck 128 64 131 512 = true := by decide +kernel
theorem bucket132 : secantCheck 128 64 132 512 = true := by decide +kernel
theorem bucket133 : secantCheck 128 64 133 512 = true := by decide +kernel
theorem bucket134 : secantCheck 128 64 134 512 = true := by decide +kernel
theorem bucket135 : secantCheck 128 64 135 512 = true := by decide +kernel
theorem bucket136 : secantCheck 128 64 136 512 = true := by decide +kernel
theorem bucket137 : secantCheck 128 64 137 512 = true := by decide +kernel
theorem bucket138 : secantCheck 128 64 138 512 = true := by decide +kernel
theorem bucket139 : secantCheck 128 64 139 512 = true := by decide +kernel
theorem bucket140 : secantCheck 128 64 140 512 = true := by decide +kernel
theorem bucket141 : secantCheck 128 64 141 512 = true := by decide +kernel
theorem bucket142 : secantCheck 128 64 142 512 = true := by decide +kernel
theorem bucket143 : secantCheck 128 64 143 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip08
