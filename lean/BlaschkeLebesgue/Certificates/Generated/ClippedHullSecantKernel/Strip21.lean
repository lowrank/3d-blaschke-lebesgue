module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 336 through 351 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip21

theorem bucket336 : secantCheck 128 64 336 512 = true := by decide +kernel
theorem bucket337 : secantCheck 128 64 337 512 = true := by decide +kernel
theorem bucket338 : secantCheck 128 64 338 512 = true := by decide +kernel
theorem bucket339 : secantCheck 128 64 339 512 = true := by decide +kernel
theorem bucket340 : secantCheck 128 64 340 512 = true := by decide +kernel
theorem bucket341 : secantCheck 128 64 341 512 = true := by decide +kernel
theorem bucket342 : secantCheck 128 64 342 512 = true := by decide +kernel
theorem bucket343 : secantCheck 128 64 343 512 = true := by decide +kernel
theorem bucket344 : secantCheck 128 64 344 512 = true := by decide +kernel
theorem bucket345 : secantCheck 128 64 345 512 = true := by decide +kernel
theorem bucket346 : secantCheck 128 64 346 512 = true := by decide +kernel
theorem bucket347 : secantCheck 128 64 347 512 = true := by decide +kernel
theorem bucket348 : secantCheck 128 64 348 512 = true := by decide +kernel
theorem bucket349 : secantCheck 128 64 349 512 = true := by decide +kernel
theorem bucket350 : secantCheck 128 64 350 512 = true := by decide +kernel
theorem bucket351 : secantCheck 128 64 351 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip21
