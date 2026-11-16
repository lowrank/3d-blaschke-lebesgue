module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 112 through 127 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip07

theorem bucket112 : secantCheck 128 64 112 512 = true := by decide +kernel
theorem bucket113 : secantCheck 128 64 113 512 = true := by decide +kernel
theorem bucket114 : secantCheck 128 64 114 512 = true := by decide +kernel
theorem bucket115 : secantCheck 128 64 115 512 = true := by decide +kernel
theorem bucket116 : secantCheck 128 64 116 512 = true := by decide +kernel
theorem bucket117 : secantCheck 128 64 117 512 = true := by decide +kernel
theorem bucket118 : secantCheck 128 64 118 512 = true := by decide +kernel
theorem bucket119 : secantCheck 128 64 119 512 = true := by decide +kernel
theorem bucket120 : secantCheck 128 64 120 512 = true := by decide +kernel
theorem bucket121 : secantCheck 128 64 121 512 = true := by decide +kernel
theorem bucket122 : secantCheck 128 64 122 512 = true := by decide +kernel
theorem bucket123 : secantCheck 128 64 123 512 = true := by decide +kernel
theorem bucket124 : secantCheck 128 64 124 512 = true := by decide +kernel
theorem bucket125 : secantCheck 128 64 125 512 = true := by decide +kernel
theorem bucket126 : secantCheck 128 64 126 512 = true := by decide +kernel
theorem bucket127 : secantCheck 128 64 127 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip07
