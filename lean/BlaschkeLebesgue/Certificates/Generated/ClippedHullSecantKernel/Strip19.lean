module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 304 through 319 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip19

theorem bucket304 : secantCheck 128 64 304 512 = true := by decide +kernel
theorem bucket305 : secantCheck 128 64 305 512 = true := by decide +kernel
theorem bucket306 : secantCheck 128 64 306 512 = true := by decide +kernel
theorem bucket307 : secantCheck 128 64 307 512 = true := by decide +kernel
theorem bucket308 : secantCheck 128 64 308 512 = true := by decide +kernel
theorem bucket309 : secantCheck 128 64 309 512 = true := by decide +kernel
theorem bucket310 : secantCheck 128 64 310 512 = true := by decide +kernel
theorem bucket311 : secantCheck 128 64 311 512 = true := by decide +kernel
theorem bucket312 : secantCheck 128 64 312 512 = true := by decide +kernel
theorem bucket313 : secantCheck 128 64 313 512 = true := by decide +kernel
theorem bucket314 : secantCheck 128 64 314 512 = true := by decide +kernel
theorem bucket315 : secantCheck 128 64 315 512 = true := by decide +kernel
theorem bucket316 : secantCheck 128 64 316 512 = true := by decide +kernel
theorem bucket317 : secantCheck 128 64 317 512 = true := by decide +kernel
theorem bucket318 : secantCheck 128 64 318 512 = true := by decide +kernel
theorem bucket319 : secantCheck 128 64 319 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip19
