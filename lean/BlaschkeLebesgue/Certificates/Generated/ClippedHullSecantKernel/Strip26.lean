module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 416 through 431 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip26

theorem bucket416 : secantCheck 128 64 416 512 = true := by decide +kernel
theorem bucket417 : secantCheck 128 64 417 512 = true := by decide +kernel
theorem bucket418 : secantCheck 128 64 418 512 = true := by decide +kernel
theorem bucket419 : secantCheck 128 64 419 512 = true := by decide +kernel
theorem bucket420 : secantCheck 128 64 420 512 = true := by decide +kernel
theorem bucket421 : secantCheck 128 64 421 512 = true := by decide +kernel
theorem bucket422 : secantCheck 128 64 422 512 = true := by decide +kernel
theorem bucket423 : secantCheck 128 64 423 512 = true := by decide +kernel
theorem bucket424 : secantCheck 128 64 424 512 = true := by decide +kernel
theorem bucket425 : secantCheck 128 64 425 512 = true := by decide +kernel
theorem bucket426 : secantCheck 128 64 426 512 = true := by decide +kernel
theorem bucket427 : secantCheck 128 64 427 512 = true := by decide +kernel
theorem bucket428 : secantCheck 128 64 428 512 = true := by decide +kernel
theorem bucket429 : secantCheck 128 64 429 512 = true := by decide +kernel
theorem bucket430 : secantCheck 128 64 430 512 = true := by decide +kernel
theorem bucket431 : secantCheck 128 64 431 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip26
