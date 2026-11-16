module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 400 through 415 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip25

theorem bucket400 : secantCheck 128 64 400 512 = true := by decide +kernel
theorem bucket401 : secantCheck 128 64 401 512 = true := by decide +kernel
theorem bucket402 : secantCheck 128 64 402 512 = true := by decide +kernel
theorem bucket403 : secantCheck 128 64 403 512 = true := by decide +kernel
theorem bucket404 : secantCheck 128 64 404 512 = true := by decide +kernel
theorem bucket405 : secantCheck 128 64 405 512 = true := by decide +kernel
theorem bucket406 : secantCheck 128 64 406 512 = true := by decide +kernel
theorem bucket407 : secantCheck 128 64 407 512 = true := by decide +kernel
theorem bucket408 : secantCheck 128 64 408 512 = true := by decide +kernel
theorem bucket409 : secantCheck 128 64 409 512 = true := by decide +kernel
theorem bucket410 : secantCheck 128 64 410 512 = true := by decide +kernel
theorem bucket411 : secantCheck 128 64 411 512 = true := by decide +kernel
theorem bucket412 : secantCheck 128 64 412 512 = true := by decide +kernel
theorem bucket413 : secantCheck 128 64 413 512 = true := by decide +kernel
theorem bucket414 : secantCheck 128 64 414 512 = true := by decide +kernel
theorem bucket415 : secantCheck 128 64 415 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip25
