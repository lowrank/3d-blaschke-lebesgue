module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 176 through 191 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip11

theorem bucket176 : secantCheck 128 64 176 512 = true := by decide +kernel
theorem bucket177 : secantCheck 128 64 177 512 = true := by decide +kernel
theorem bucket178 : secantCheck 128 64 178 512 = true := by decide +kernel
theorem bucket179 : secantCheck 128 64 179 512 = true := by decide +kernel
theorem bucket180 : secantCheck 128 64 180 512 = true := by decide +kernel
theorem bucket181 : secantCheck 128 64 181 512 = true := by decide +kernel
theorem bucket182 : secantCheck 128 64 182 512 = true := by decide +kernel
theorem bucket183 : secantCheck 128 64 183 512 = true := by decide +kernel
theorem bucket184 : secantCheck 128 64 184 512 = true := by decide +kernel
theorem bucket185 : secantCheck 128 64 185 512 = true := by decide +kernel
theorem bucket186 : secantCheck 128 64 186 512 = true := by decide +kernel
theorem bucket187 : secantCheck 128 64 187 512 = true := by decide +kernel
theorem bucket188 : secantCheck 128 64 188 512 = true := by decide +kernel
theorem bucket189 : secantCheck 128 64 189 512 = true := by decide +kernel
theorem bucket190 : secantCheck 128 64 190 512 = true := by decide +kernel
theorem bucket191 : secantCheck 128 64 191 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip11
