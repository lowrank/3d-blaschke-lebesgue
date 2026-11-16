module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 160 through 175 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip10

theorem bucket160 : secantCheck 128 64 160 512 = true := by decide +kernel
theorem bucket161 : secantCheck 128 64 161 512 = true := by decide +kernel
theorem bucket162 : secantCheck 128 64 162 512 = true := by decide +kernel
theorem bucket163 : secantCheck 128 64 163 512 = true := by decide +kernel
theorem bucket164 : secantCheck 128 64 164 512 = true := by decide +kernel
theorem bucket165 : secantCheck 128 64 165 512 = true := by decide +kernel
theorem bucket166 : secantCheck 128 64 166 512 = true := by decide +kernel
theorem bucket167 : secantCheck 128 64 167 512 = true := by decide +kernel
theorem bucket168 : secantCheck 128 64 168 512 = true := by decide +kernel
theorem bucket169 : secantCheck 128 64 169 512 = true := by decide +kernel
theorem bucket170 : secantCheck 128 64 170 512 = true := by decide +kernel
theorem bucket171 : secantCheck 128 64 171 512 = true := by decide +kernel
theorem bucket172 : secantCheck 128 64 172 512 = true := by decide +kernel
theorem bucket173 : secantCheck 128 64 173 512 = true := by decide +kernel
theorem bucket174 : secantCheck 128 64 174 512 = true := by decide +kernel
theorem bucket175 : secantCheck 128 64 175 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip10
