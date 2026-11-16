module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets 0 through 15 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip00

theorem bucket000 : secantCheck 128 64 0 512 = true := by decide +kernel
theorem bucket001 : secantCheck 128 64 1 512 = true := by decide +kernel
theorem bucket002 : secantCheck 128 64 2 512 = true := by decide +kernel
theorem bucket003 : secantCheck 128 64 3 512 = true := by decide +kernel
theorem bucket004 : secantCheck 128 64 4 512 = true := by decide +kernel
theorem bucket005 : secantCheck 128 64 5 512 = true := by decide +kernel
theorem bucket006 : secantCheck 128 64 6 512 = true := by decide +kernel
theorem bucket007 : secantCheck 128 64 7 512 = true := by decide +kernel
theorem bucket008 : secantCheck 128 64 8 512 = true := by decide +kernel
theorem bucket009 : secantCheck 128 64 9 512 = true := by decide +kernel
theorem bucket010 : secantCheck 128 64 10 512 = true := by decide +kernel
theorem bucket011 : secantCheck 128 64 11 512 = true := by decide +kernel
theorem bucket012 : secantCheck 128 64 12 512 = true := by decide +kernel
theorem bucket013 : secantCheck 128 64 13 512 = true := by decide +kernel
theorem bucket014 : secantCheck 128 64 14 512 = true := by decide +kernel
theorem bucket015 : secantCheck 128 64 15 512 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip00
