module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 448 through 463 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip28

theorem bucket448 : secantCheck 128 64 448 512 = true := by decide +kernel
theorem bucket449 : secantCheck 128 64 449 512 = true := by decide +kernel
theorem bucket450 : secantCheck 128 64 450 512 = true := by decide +kernel
theorem bucket451 : secantCheck 128 64 451 512 = true := by decide +kernel
theorem bucket452 : secantCheck 128 64 452 512 = true := by decide +kernel
theorem bucket453 : secantCheck 128 64 453 512 = true := by decide +kernel
theorem bucket454 : secantCheck 128 64 454 512 = true := by decide +kernel
theorem bucket455 : secantCheck 128 64 455 512 = true := by decide +kernel
theorem bucket456 : secantCheck 128 64 456 512 = true := by decide +kernel
theorem bucket457 : secantCheck 128 64 457 512 = true := by decide +kernel
theorem bucket458 : secantCheck 128 64 458 512 = true := by decide +kernel
theorem bucket459 : secantCheck 128 64 459 512 = true := by decide +kernel
theorem bucket460 : secantCheck 128 64 460 512 = true := by decide +kernel
theorem bucket461 : secantCheck 128 64 461 512 = true := by decide +kernel
theorem bucket462 : secantCheck 128 64 462 512 = true := by decide +kernel
theorem bucket463 : secantCheck 128 64 463 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip28
