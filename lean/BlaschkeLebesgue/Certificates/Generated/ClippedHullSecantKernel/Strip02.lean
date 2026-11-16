module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 32 through 47 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip02

theorem bucket032 : secantCheck 128 64 32 512 = true := by decide +kernel
theorem bucket033 : secantCheck 128 64 33 512 = true := by decide +kernel
theorem bucket034 : secantCheck 128 64 34 512 = true := by decide +kernel
theorem bucket035 : secantCheck 128 64 35 512 = true := by decide +kernel
theorem bucket036 : secantCheck 128 64 36 512 = true := by decide +kernel
theorem bucket037 : secantCheck 128 64 37 512 = true := by decide +kernel
theorem bucket038 : secantCheck 128 64 38 512 = true := by decide +kernel
theorem bucket039 : secantCheck 128 64 39 512 = true := by decide +kernel
theorem bucket040 : secantCheck 128 64 40 512 = true := by decide +kernel
theorem bucket041 : secantCheck 128 64 41 512 = true := by decide +kernel
theorem bucket042 : secantCheck 128 64 42 512 = true := by decide +kernel
theorem bucket043 : secantCheck 128 64 43 512 = true := by decide +kernel
theorem bucket044 : secantCheck 128 64 44 512 = true := by decide +kernel
theorem bucket045 : secantCheck 128 64 45 512 = true := by decide +kernel
theorem bucket046 : secantCheck 128 64 46 512 = true := by decide +kernel
theorem bucket047 : secantCheck 128 64 47 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip02
