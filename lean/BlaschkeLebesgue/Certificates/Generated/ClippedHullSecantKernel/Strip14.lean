module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 224 through 239 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip14

theorem bucket224 : secantCheck 128 64 224 512 = true := by decide +kernel
theorem bucket225 : secantCheck 128 64 225 512 = true := by decide +kernel
theorem bucket226 : secantCheck 128 64 226 512 = true := by decide +kernel
theorem bucket227 : secantCheck 128 64 227 512 = true := by decide +kernel
theorem bucket228 : secantCheck 128 64 228 512 = true := by decide +kernel
theorem bucket229 : secantCheck 128 64 229 512 = true := by decide +kernel
theorem bucket230 : secantCheck 128 64 230 512 = true := by decide +kernel
theorem bucket231 : secantCheck 128 64 231 512 = true := by decide +kernel
theorem bucket232 : secantCheck 128 64 232 512 = true := by decide +kernel
theorem bucket233 : secantCheck 128 64 233 512 = true := by decide +kernel
theorem bucket234 : secantCheck 128 64 234 512 = true := by decide +kernel
theorem bucket235 : secantCheck 128 64 235 512 = true := by decide +kernel
theorem bucket236 : secantCheck 128 64 236 512 = true := by decide +kernel
theorem bucket237 : secantCheck 128 64 237 512 = true := by decide +kernel
theorem bucket238 : secantCheck 128 64 238 512 = true := by decide +kernel
theorem bucket239 : secantCheck 128 64 239 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip14
