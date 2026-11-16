module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 64 through 79 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip04

theorem bucket064 : secantCheck 128 64 64 512 = true := by decide +kernel
theorem bucket065 : secantCheck 128 64 65 512 = true := by decide +kernel
theorem bucket066 : secantCheck 128 64 66 512 = true := by decide +kernel
theorem bucket067 : secantCheck 128 64 67 512 = true := by decide +kernel
theorem bucket068 : secantCheck 128 64 68 512 = true := by decide +kernel
theorem bucket069 : secantCheck 128 64 69 512 = true := by decide +kernel
theorem bucket070 : secantCheck 128 64 70 512 = true := by decide +kernel
theorem bucket071 : secantCheck 128 64 71 512 = true := by decide +kernel
theorem bucket072 : secantCheck 128 64 72 512 = true := by decide +kernel
theorem bucket073 : secantCheck 128 64 73 512 = true := by decide +kernel
theorem bucket074 : secantCheck 128 64 74 512 = true := by decide +kernel
theorem bucket075 : secantCheck 128 64 75 512 = true := by decide +kernel
theorem bucket076 : secantCheck 128 64 76 512 = true := by decide +kernel
theorem bucket077 : secantCheck 128 64 77 512 = true := by decide +kernel
theorem bucket078 : secantCheck 128 64 78 512 = true := by decide +kernel
theorem bucket079 : secantCheck 128 64 79 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip04
