module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 240 through 255 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip15

theorem bucket240 : secantCheck 128 64 240 512 = true := by decide +kernel
theorem bucket241 : secantCheck 128 64 241 512 = true := by decide +kernel
theorem bucket242 : secantCheck 128 64 242 512 = true := by decide +kernel
theorem bucket243 : secantCheck 128 64 243 512 = true := by decide +kernel
theorem bucket244 : secantCheck 128 64 244 512 = true := by decide +kernel
theorem bucket245 : secantCheck 128 64 245 512 = true := by decide +kernel
theorem bucket246 : secantCheck 128 64 246 512 = true := by decide +kernel
theorem bucket247 : secantCheck 128 64 247 512 = true := by decide +kernel
theorem bucket248 : secantCheck 128 64 248 512 = true := by decide +kernel
theorem bucket249 : secantCheck 128 64 249 512 = true := by decide +kernel
theorem bucket250 : secantCheck 128 64 250 512 = true := by decide +kernel
theorem bucket251 : secantCheck 128 64 251 512 = true := by decide +kernel
theorem bucket252 : secantCheck 128 64 252 512 = true := by decide +kernel
theorem bucket253 : secantCheck 128 64 253 512 = true := by decide +kernel
theorem bucket254 : secantCheck 128 64 254 512 = true := by decide +kernel
theorem bucket255 : secantCheck 128 64 255 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip15
