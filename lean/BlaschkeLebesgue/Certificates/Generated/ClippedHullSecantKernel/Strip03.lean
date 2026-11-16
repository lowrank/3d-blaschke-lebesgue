module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 48 through 63 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip03

theorem bucket048 : secantCheck 128 64 48 512 = true := by decide +kernel
theorem bucket049 : secantCheck 128 64 49 512 = true := by decide +kernel
theorem bucket050 : secantCheck 128 64 50 512 = true := by decide +kernel
theorem bucket051 : secantCheck 128 64 51 512 = true := by decide +kernel
theorem bucket052 : secantCheck 128 64 52 512 = true := by decide +kernel
theorem bucket053 : secantCheck 128 64 53 512 = true := by decide +kernel
theorem bucket054 : secantCheck 128 64 54 512 = true := by decide +kernel
theorem bucket055 : secantCheck 128 64 55 512 = true := by decide +kernel
theorem bucket056 : secantCheck 128 64 56 512 = true := by decide +kernel
theorem bucket057 : secantCheck 128 64 57 512 = true := by decide +kernel
theorem bucket058 : secantCheck 128 64 58 512 = true := by decide +kernel
theorem bucket059 : secantCheck 128 64 59 512 = true := by decide +kernel
theorem bucket060 : secantCheck 128 64 60 512 = true := by decide +kernel
theorem bucket061 : secantCheck 128 64 61 512 = true := by decide +kernel
theorem bucket062 : secantCheck 128 64 62 512 = true := by decide +kernel
theorem bucket063 : secantCheck 128 64 63 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip03
