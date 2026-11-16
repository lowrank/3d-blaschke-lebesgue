module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 368 through 383 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip23

theorem bucket368 : secantCheck 128 64 368 512 = true := by decide +kernel
theorem bucket369 : secantCheck 128 64 369 512 = true := by decide +kernel
theorem bucket370 : secantCheck 128 64 370 512 = true := by decide +kernel
theorem bucket371 : secantCheck 128 64 371 512 = true := by decide +kernel
theorem bucket372 : secantCheck 128 64 372 512 = true := by decide +kernel
theorem bucket373 : secantCheck 128 64 373 512 = true := by decide +kernel
theorem bucket374 : secantCheck 128 64 374 512 = true := by decide +kernel
theorem bucket375 : secantCheck 128 64 375 512 = true := by decide +kernel
theorem bucket376 : secantCheck 128 64 376 512 = true := by decide +kernel
theorem bucket377 : secantCheck 128 64 377 512 = true := by decide +kernel
theorem bucket378 : secantCheck 128 64 378 512 = true := by decide +kernel
theorem bucket379 : secantCheck 128 64 379 512 = true := by decide +kernel
theorem bucket380 : secantCheck 128 64 380 512 = true := by decide +kernel
theorem bucket381 : secantCheck 128 64 381 512 = true := by decide +kernel
theorem bucket382 : secantCheck 128 64 382 512 = true := by decide +kernel
theorem bucket383 : secantCheck 128 64 383 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip23
