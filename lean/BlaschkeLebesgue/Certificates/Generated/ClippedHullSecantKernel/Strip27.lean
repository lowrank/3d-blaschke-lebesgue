module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 432 through 447 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip27

theorem bucket432 : secantCheck 128 64 432 512 = true := by decide +kernel
theorem bucket433 : secantCheck 128 64 433 512 = true := by decide +kernel
theorem bucket434 : secantCheck 128 64 434 512 = true := by decide +kernel
theorem bucket435 : secantCheck 128 64 435 512 = true := by decide +kernel
theorem bucket436 : secantCheck 128 64 436 512 = true := by decide +kernel
theorem bucket437 : secantCheck 128 64 437 512 = true := by decide +kernel
theorem bucket438 : secantCheck 128 64 438 512 = true := by decide +kernel
theorem bucket439 : secantCheck 128 64 439 512 = true := by decide +kernel
theorem bucket440 : secantCheck 128 64 440 512 = true := by decide +kernel
theorem bucket441 : secantCheck 128 64 441 512 = true := by decide +kernel
theorem bucket442 : secantCheck 128 64 442 512 = true := by decide +kernel
theorem bucket443 : secantCheck 128 64 443 512 = true := by decide +kernel
theorem bucket444 : secantCheck 128 64 444 512 = true := by decide +kernel
theorem bucket445 : secantCheck 128 64 445 512 = true := by decide +kernel
theorem bucket446 : secantCheck 128 64 446 512 = true := by decide +kernel
theorem bucket447 : secantCheck 128 64 447 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip27
