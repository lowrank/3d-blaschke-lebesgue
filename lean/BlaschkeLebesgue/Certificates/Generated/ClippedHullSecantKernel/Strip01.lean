module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 16 through 31 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip01

theorem bucket016 : secantCheck 128 64 16 512 = true := by decide +kernel
theorem bucket017 : secantCheck 128 64 17 512 = true := by decide +kernel
theorem bucket018 : secantCheck 128 64 18 512 = true := by decide +kernel
theorem bucket019 : secantCheck 128 64 19 512 = true := by decide +kernel
theorem bucket020 : secantCheck 128 64 20 512 = true := by decide +kernel
theorem bucket021 : secantCheck 128 64 21 512 = true := by decide +kernel
theorem bucket022 : secantCheck 128 64 22 512 = true := by decide +kernel
theorem bucket023 : secantCheck 128 64 23 512 = true := by decide +kernel
theorem bucket024 : secantCheck 128 64 24 512 = true := by decide +kernel
theorem bucket025 : secantCheck 128 64 25 512 = true := by decide +kernel
theorem bucket026 : secantCheck 128 64 26 512 = true := by decide +kernel
theorem bucket027 : secantCheck 128 64 27 512 = true := by decide +kernel
theorem bucket028 : secantCheck 128 64 28 512 = true := by decide +kernel
theorem bucket029 : secantCheck 128 64 29 512 = true := by decide +kernel
theorem bucket030 : secantCheck 128 64 30 512 = true := by decide +kernel
theorem bucket031 : secantCheck 128 64 31 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip01
