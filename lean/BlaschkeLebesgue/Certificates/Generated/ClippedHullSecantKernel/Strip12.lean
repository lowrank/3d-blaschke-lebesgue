module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 192 through 207 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip12

theorem bucket192 : secantCheck 128 64 192 512 = true := by decide +kernel
theorem bucket193 : secantCheck 128 64 193 512 = true := by decide +kernel
theorem bucket194 : secantCheck 128 64 194 512 = true := by decide +kernel
theorem bucket195 : secantCheck 128 64 195 512 = true := by decide +kernel
theorem bucket196 : secantCheck 128 64 196 512 = true := by decide +kernel
theorem bucket197 : secantCheck 128 64 197 512 = true := by decide +kernel
theorem bucket198 : secantCheck 128 64 198 512 = true := by decide +kernel
theorem bucket199 : secantCheck 128 64 199 512 = true := by decide +kernel
theorem bucket200 : secantCheck 128 64 200 512 = true := by decide +kernel
theorem bucket201 : secantCheck 128 64 201 512 = true := by decide +kernel
theorem bucket202 : secantCheck 128 64 202 512 = true := by decide +kernel
theorem bucket203 : secantCheck 128 64 203 512 = true := by decide +kernel
theorem bucket204 : secantCheck 128 64 204 512 = true := by decide +kernel
theorem bucket205 : secantCheck 128 64 205 512 = true := by decide +kernel
theorem bucket206 : secantCheck 128 64 206 512 = true := by decide +kernel
theorem bucket207 : secantCheck 128 64 207 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip12
