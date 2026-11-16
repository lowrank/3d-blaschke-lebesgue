module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 480 through 495 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip30

theorem bucket480 : secantCheck 128 64 480 512 = true := by decide +kernel
theorem bucket481 : secantCheck 128 64 481 512 = true := by decide +kernel
theorem bucket482 : secantCheck 128 64 482 512 = true := by decide +kernel
theorem bucket483 : secantCheck 128 64 483 512 = true := by decide +kernel
theorem bucket484 : secantCheck 128 64 484 512 = true := by decide +kernel
theorem bucket485 : secantCheck 128 64 485 512 = true := by decide +kernel
theorem bucket486 : secantCheck 128 64 486 512 = true := by decide +kernel
theorem bucket487 : secantCheck 128 64 487 512 = true := by decide +kernel
theorem bucket488 : secantCheck 128 64 488 512 = true := by decide +kernel
theorem bucket489 : secantCheck 128 64 489 512 = true := by decide +kernel
theorem bucket490 : secantCheck 128 64 490 512 = true := by decide +kernel
theorem bucket491 : secantCheck 128 64 491 512 = true := by decide +kernel
theorem bucket492 : secantCheck 128 64 492 512 = true := by decide +kernel
theorem bucket493 : secantCheck 128 64 493 512 = true := by decide +kernel
theorem bucket494 : secantCheck 128 64 494 512 = true := by decide +kernel
theorem bucket495 : secantCheck 128 64 495 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip30
