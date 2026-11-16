module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 208 through 223 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip13

theorem bucket208 : secantCheck 128 64 208 512 = true := by decide +kernel
theorem bucket209 : secantCheck 128 64 209 512 = true := by decide +kernel
theorem bucket210 : secantCheck 128 64 210 512 = true := by decide +kernel
theorem bucket211 : secantCheck 128 64 211 512 = true := by decide +kernel
theorem bucket212 : secantCheck 128 64 212 512 = true := by decide +kernel
theorem bucket213 : secantCheck 128 64 213 512 = true := by decide +kernel
theorem bucket214 : secantCheck 128 64 214 512 = true := by decide +kernel
theorem bucket215 : secantCheck 128 64 215 512 = true := by decide +kernel
theorem bucket216 : secantCheck 128 64 216 512 = true := by decide +kernel
theorem bucket217 : secantCheck 128 64 217 512 = true := by decide +kernel
theorem bucket218 : secantCheck 128 64 218 512 = true := by decide +kernel
theorem bucket219 : secantCheck 128 64 219 512 = true := by decide +kernel
theorem bucket220 : secantCheck 128 64 220 512 = true := by decide +kernel
theorem bucket221 : secantCheck 128 64 221 512 = true := by decide +kernel
theorem bucket222 : secantCheck 128 64 222 512 = true := by decide +kernel
theorem bucket223 : secantCheck 128 64 223 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip13
