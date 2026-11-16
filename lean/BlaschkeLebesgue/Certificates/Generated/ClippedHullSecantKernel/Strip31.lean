module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 496 through 511 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip31

theorem bucket496 : secantCheck 128 64 496 512 = true := by decide +kernel
theorem bucket497 : secantCheck 128 64 497 512 = true := by decide +kernel
theorem bucket498 : secantCheck 128 64 498 512 = true := by decide +kernel
theorem bucket499 : secantCheck 128 64 499 512 = true := by decide +kernel
theorem bucket500 : secantCheck 128 64 500 512 = true := by decide +kernel
theorem bucket501 : secantCheck 128 64 501 512 = true := by decide +kernel
theorem bucket502 : secantCheck 128 64 502 512 = true := by decide +kernel
theorem bucket503 : secantCheck 128 64 503 512 = true := by decide +kernel
theorem bucket504 : secantCheck 128 64 504 512 = true := by decide +kernel
theorem bucket505 : secantCheck 128 64 505 512 = true := by decide +kernel
theorem bucket506 : secantCheck 128 64 506 512 = true := by decide +kernel
theorem bucket507 : secantCheck 128 64 507 512 = true := by decide +kernel
theorem bucket508 : secantCheck 128 64 508 512 = true := by decide +kernel
theorem bucket509 : secantCheck 128 64 509 512 = true := by decide +kernel
theorem bucket510 : secantCheck 128 64 510 512 = true := by decide +kernel
theorem bucket511 : secantCheck 128 64 511 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip31
