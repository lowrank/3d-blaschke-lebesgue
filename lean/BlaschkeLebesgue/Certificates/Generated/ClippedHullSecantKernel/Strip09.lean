module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 144 through 159 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip09

theorem bucket144 : secantCheck 128 64 144 512 = true := by decide +kernel
theorem bucket145 : secantCheck 128 64 145 512 = true := by decide +kernel
theorem bucket146 : secantCheck 128 64 146 512 = true := by decide +kernel
theorem bucket147 : secantCheck 128 64 147 512 = true := by decide +kernel
theorem bucket148 : secantCheck 128 64 148 512 = true := by decide +kernel
theorem bucket149 : secantCheck 128 64 149 512 = true := by decide +kernel
theorem bucket150 : secantCheck 128 64 150 512 = true := by decide +kernel
theorem bucket151 : secantCheck 128 64 151 512 = true := by decide +kernel
theorem bucket152 : secantCheck 128 64 152 512 = true := by decide +kernel
theorem bucket153 : secantCheck 128 64 153 512 = true := by decide +kernel
theorem bucket154 : secantCheck 128 64 154 512 = true := by decide +kernel
theorem bucket155 : secantCheck 128 64 155 512 = true := by decide +kernel
theorem bucket156 : secantCheck 128 64 156 512 = true := by decide +kernel
theorem bucket157 : secantCheck 128 64 157 512 = true := by decide +kernel
theorem bucket158 : secantCheck 128 64 158 512 = true := by decide +kernel
theorem bucket159 : secantCheck 128 64 159 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip09
