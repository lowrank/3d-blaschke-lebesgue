module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 384 through 399 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip24

theorem bucket384 : secantCheck 128 64 384 512 = true := by decide +kernel
theorem bucket385 : secantCheck 128 64 385 512 = true := by decide +kernel
theorem bucket386 : secantCheck 128 64 386 512 = true := by decide +kernel
theorem bucket387 : secantCheck 128 64 387 512 = true := by decide +kernel
theorem bucket388 : secantCheck 128 64 388 512 = true := by decide +kernel
theorem bucket389 : secantCheck 128 64 389 512 = true := by decide +kernel
theorem bucket390 : secantCheck 128 64 390 512 = true := by decide +kernel
theorem bucket391 : secantCheck 128 64 391 512 = true := by decide +kernel
theorem bucket392 : secantCheck 128 64 392 512 = true := by decide +kernel
theorem bucket393 : secantCheck 128 64 393 512 = true := by decide +kernel
theorem bucket394 : secantCheck 128 64 394 512 = true := by decide +kernel
theorem bucket395 : secantCheck 128 64 395 512 = true := by decide +kernel
theorem bucket396 : secantCheck 128 64 396 512 = true := by decide +kernel
theorem bucket397 : secantCheck 128 64 397 512 = true := by decide +kernel
theorem bucket398 : secantCheck 128 64 398 512 = true := by decide +kernel
theorem bucket399 : secantCheck 128 64 399 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip24
