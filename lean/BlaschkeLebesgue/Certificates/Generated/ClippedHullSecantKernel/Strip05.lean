module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 80 through 95 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip05

theorem bucket080 : secantCheck 128 64 80 512 = true := by decide +kernel
theorem bucket081 : secantCheck 128 64 81 512 = true := by decide +kernel
theorem bucket082 : secantCheck 128 64 82 512 = true := by decide +kernel
theorem bucket083 : secantCheck 128 64 83 512 = true := by decide +kernel
theorem bucket084 : secantCheck 128 64 84 512 = true := by decide +kernel
theorem bucket085 : secantCheck 128 64 85 512 = true := by decide +kernel
theorem bucket086 : secantCheck 128 64 86 512 = true := by decide +kernel
theorem bucket087 : secantCheck 128 64 87 512 = true := by decide +kernel
theorem bucket088 : secantCheck 128 64 88 512 = true := by decide +kernel
theorem bucket089 : secantCheck 128 64 89 512 = true := by decide +kernel
theorem bucket090 : secantCheck 128 64 90 512 = true := by decide +kernel
theorem bucket091 : secantCheck 128 64 91 512 = true := by decide +kernel
theorem bucket092 : secantCheck 128 64 92 512 = true := by decide +kernel
theorem bucket093 : secantCheck 128 64 93 512 = true := by decide +kernel
theorem bucket094 : secantCheck 128 64 94 512 = true := by decide +kernel
theorem bucket095 : secantCheck 128 64 95 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip05
