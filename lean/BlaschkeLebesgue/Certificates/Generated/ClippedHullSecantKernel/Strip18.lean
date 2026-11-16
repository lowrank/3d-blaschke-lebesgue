module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 288 through 303 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip18

theorem bucket288 : secantCheck 128 64 288 512 = true := by decide +kernel
theorem bucket289 : secantCheck 128 64 289 512 = true := by decide +kernel
theorem bucket290 : secantCheck 128 64 290 512 = true := by decide +kernel
theorem bucket291 : secantCheck 128 64 291 512 = true := by decide +kernel
theorem bucket292 : secantCheck 128 64 292 512 = true := by decide +kernel
theorem bucket293 : secantCheck 128 64 293 512 = true := by decide +kernel
theorem bucket294 : secantCheck 128 64 294 512 = true := by decide +kernel
theorem bucket295 : secantCheck 128 64 295 512 = true := by decide +kernel
theorem bucket296 : secantCheck 128 64 296 512 = true := by decide +kernel
theorem bucket297 : secantCheck 128 64 297 512 = true := by decide +kernel
theorem bucket298 : secantCheck 128 64 298 512 = true := by decide +kernel
theorem bucket299 : secantCheck 128 64 299 512 = true := by decide +kernel
theorem bucket300 : secantCheck 128 64 300 512 = true := by decide +kernel
theorem bucket301 : secantCheck 128 64 301 512 = true := by decide +kernel
theorem bucket302 : secantCheck 128 64 302 512 = true := by decide +kernel
theorem bucket303 : secantCheck 128 64 303 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip18
