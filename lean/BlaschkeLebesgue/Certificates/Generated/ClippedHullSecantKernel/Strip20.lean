module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 320 through 335 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip20

theorem bucket320 : secantCheck 128 64 320 512 = true := by decide +kernel
theorem bucket321 : secantCheck 128 64 321 512 = true := by decide +kernel
theorem bucket322 : secantCheck 128 64 322 512 = true := by decide +kernel
theorem bucket323 : secantCheck 128 64 323 512 = true := by decide +kernel
theorem bucket324 : secantCheck 128 64 324 512 = true := by decide +kernel
theorem bucket325 : secantCheck 128 64 325 512 = true := by decide +kernel
theorem bucket326 : secantCheck 128 64 326 512 = true := by decide +kernel
theorem bucket327 : secantCheck 128 64 327 512 = true := by decide +kernel
theorem bucket328 : secantCheck 128 64 328 512 = true := by decide +kernel
theorem bucket329 : secantCheck 128 64 329 512 = true := by decide +kernel
theorem bucket330 : secantCheck 128 64 330 512 = true := by decide +kernel
theorem bucket331 : secantCheck 128 64 331 512 = true := by decide +kernel
theorem bucket332 : secantCheck 128 64 332 512 = true := by decide +kernel
theorem bucket333 : secantCheck 128 64 333 512 = true := by decide +kernel
theorem bucket334 : secantCheck 128 64 334 512 = true := by decide +kernel
theorem bucket335 : secantCheck 128 64 335 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip20
