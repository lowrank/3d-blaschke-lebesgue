module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 96 through 111 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip06

theorem bucket096 : secantCheck 128 64 96 512 = true := by decide +kernel
theorem bucket097 : secantCheck 128 64 97 512 = true := by decide +kernel
theorem bucket098 : secantCheck 128 64 98 512 = true := by decide +kernel
theorem bucket099 : secantCheck 128 64 99 512 = true := by decide +kernel
theorem bucket100 : secantCheck 128 64 100 512 = true := by decide +kernel
theorem bucket101 : secantCheck 128 64 101 512 = true := by decide +kernel
theorem bucket102 : secantCheck 128 64 102 512 = true := by decide +kernel
theorem bucket103 : secantCheck 128 64 103 512 = true := by decide +kernel
theorem bucket104 : secantCheck 128 64 104 512 = true := by decide +kernel
theorem bucket105 : secantCheck 128 64 105 512 = true := by decide +kernel
theorem bucket106 : secantCheck 128 64 106 512 = true := by decide +kernel
theorem bucket107 : secantCheck 128 64 107 512 = true := by decide +kernel
theorem bucket108 : secantCheck 128 64 108 512 = true := by decide +kernel
theorem bucket109 : secantCheck 128 64 109 512 = true := by decide +kernel
theorem bucket110 : secantCheck 128 64 110 512 = true := by decide +kernel
theorem bucket111 : secantCheck 128 64 111 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip06
