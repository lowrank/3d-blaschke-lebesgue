module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 256 through 271 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip16

theorem bucket256 : secantCheck 128 64 256 512 = true := by decide +kernel
theorem bucket257 : secantCheck 128 64 257 512 = true := by decide +kernel
theorem bucket258 : secantCheck 128 64 258 512 = true := by decide +kernel
theorem bucket259 : secantCheck 128 64 259 512 = true := by decide +kernel
theorem bucket260 : secantCheck 128 64 260 512 = true := by decide +kernel
theorem bucket261 : secantCheck 128 64 261 512 = true := by decide +kernel
theorem bucket262 : secantCheck 128 64 262 512 = true := by decide +kernel
theorem bucket263 : secantCheck 128 64 263 512 = true := by decide +kernel
theorem bucket264 : secantCheck 128 64 264 512 = true := by decide +kernel
theorem bucket265 : secantCheck 128 64 265 512 = true := by decide +kernel
theorem bucket266 : secantCheck 128 64 266 512 = true := by decide +kernel
theorem bucket267 : secantCheck 128 64 267 512 = true := by decide +kernel
theorem bucket268 : secantCheck 128 64 268 512 = true := by decide +kernel
theorem bucket269 : secantCheck 128 64 269 512 = true := by decide +kernel
theorem bucket270 : secantCheck 128 64 270 512 = true := by decide +kernel
theorem bucket271 : secantCheck 128 64 271 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip16
