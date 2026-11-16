module

public import BlaschkeLebesgue.Certificates.ClippedHullCheckComputation

/-! # Kernel sign checks for clipped-hull radius strip 1 -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull.Kernel.Strip01

theorem baseline : baselineSignCheck 128 64 1 32 = true := by decide +kernel

theorem cell000 : edgeSignCheck 128 64 1 0 32 100 = true := by decide +kernel
theorem cell001 : edgeSignCheck 128 64 1 1 32 100 = true := by decide +kernel
theorem cell002 : edgeSignCheck 128 64 1 2 32 100 = true := by decide +kernel
theorem cell003 : edgeSignCheck 128 64 1 3 32 100 = true := by decide +kernel
theorem cell004 : edgeSignCheck 128 64 1 4 32 100 = true := by decide +kernel
theorem cell005 : edgeSignCheck 128 64 1 5 32 100 = true := by decide +kernel
theorem cell006 : edgeSignCheck 128 64 1 6 32 100 = true := by decide +kernel
theorem cell007 : edgeSignCheck 128 64 1 7 32 100 = true := by decide +kernel
theorem cell008 : edgeSignCheck 128 64 1 8 32 100 = true := by decide +kernel
theorem cell009 : edgeSignCheck 128 64 1 9 32 100 = true := by decide +kernel
theorem cell010 : edgeSignCheck 128 64 1 10 32 100 = true := by decide +kernel
theorem cell011 : edgeSignCheck 128 64 1 11 32 100 = true := by decide +kernel
theorem cell012 : edgeSignCheck 128 64 1 12 32 100 = true := by decide +kernel
theorem cell013 : edgeSignCheck 128 64 1 13 32 100 = true := by decide +kernel
theorem cell014 : edgeSignCheck 128 64 1 14 32 100 = true := by decide +kernel
theorem cell015 : edgeSignCheck 128 64 1 15 32 100 = true := by decide +kernel
theorem cell016 : edgeSignCheck 128 64 1 16 32 100 = true := by decide +kernel
theorem cell017 : edgeSignCheck 128 64 1 17 32 100 = true := by decide +kernel
theorem cell018 : edgeSignCheck 128 64 1 18 32 100 = true := by decide +kernel
theorem cell019 : edgeSignCheck 128 64 1 19 32 100 = true := by decide +kernel
theorem cell020 : edgeSignCheck 128 64 1 20 32 100 = true := by decide +kernel
theorem cell021 : edgeSignCheck 128 64 1 21 32 100 = true := by decide +kernel
theorem cell022 : edgeSignCheck 128 64 1 22 32 100 = true := by decide +kernel
theorem cell023 : edgeSignCheck 128 64 1 23 32 100 = true := by decide +kernel
theorem cell024 : edgeSignCheck 128 64 1 24 32 100 = true := by decide +kernel
theorem cell025 : edgeSignCheck 128 64 1 25 32 100 = true := by decide +kernel
theorem cell026 : edgeSignCheck 128 64 1 26 32 100 = true := by decide +kernel
theorem cell027 : edgeSignCheck 128 64 1 27 32 100 = true := by decide +kernel
theorem cell028 : edgeSignCheck 128 64 1 28 32 100 = true := by decide +kernel
theorem cell029 : edgeSignCheck 128 64 1 29 32 100 = true := by decide +kernel
theorem cell030 : edgeSignCheck 128 64 1 30 32 100 = true := by decide +kernel
theorem cell031 : edgeSignCheck 128 64 1 31 32 100 = true := by decide +kernel
theorem cell032 : edgeSignCheck 128 64 1 32 32 100 = true := by decide +kernel
theorem cell033 : edgeSignCheck 128 64 1 33 32 100 = true := by decide +kernel
theorem cell034 : edgeSignCheck 128 64 1 34 32 100 = true := by decide +kernel
theorem cell035 : edgeSignCheck 128 64 1 35 32 100 = true := by decide +kernel
theorem cell036 : edgeSignCheck 128 64 1 36 32 100 = true := by decide +kernel
theorem cell037 : edgeSignCheck 128 64 1 37 32 100 = true := by decide +kernel
theorem cell038 : edgeSignCheck 128 64 1 38 32 100 = true := by decide +kernel
theorem cell039 : edgeSignCheck 128 64 1 39 32 100 = true := by decide +kernel
theorem cell040 : edgeSignCheck 128 64 1 40 32 100 = true := by decide +kernel
theorem cell041 : edgeSignCheck 128 64 1 41 32 100 = true := by decide +kernel
theorem cell042 : edgeSignCheck 128 64 1 42 32 100 = true := by decide +kernel
theorem cell043 : edgeSignCheck 128 64 1 43 32 100 = true := by decide +kernel
theorem cell044 : edgeSignCheck 128 64 1 44 32 100 = true := by decide +kernel
theorem cell045 : edgeSignCheck 128 64 1 45 32 100 = true := by decide +kernel
theorem cell046 : edgeSignCheck 128 64 1 46 32 100 = true := by decide +kernel
theorem cell047 : edgeSignCheck 128 64 1 47 32 100 = true := by decide +kernel
theorem cell048 : edgeSignCheck 128 64 1 48 32 100 = true := by decide +kernel
theorem cell049 : edgeSignCheck 128 64 1 49 32 100 = true := by decide +kernel
theorem cell050 : edgeSignCheck 128 64 1 50 32 100 = true := by decide +kernel
theorem cell051 : edgeSignCheck 128 64 1 51 32 100 = true := by decide +kernel
theorem cell052 : edgeSignCheck 128 64 1 52 32 100 = true := by decide +kernel
theorem cell053 : edgeSignCheck 128 64 1 53 32 100 = true := by decide +kernel
theorem cell054 : edgeSignCheck 128 64 1 54 32 100 = true := by decide +kernel
theorem cell055 : edgeSignCheck 128 64 1 55 32 100 = true := by decide +kernel
theorem cell056 : edgeSignCheck 128 64 1 56 32 100 = true := by decide +kernel
theorem cell057 : edgeSignCheck 128 64 1 57 32 100 = true := by decide +kernel
theorem cell058 : edgeSignCheck 128 64 1 58 32 100 = true := by decide +kernel
theorem cell059 : edgeSignCheck 128 64 1 59 32 100 = true := by decide +kernel
theorem cell060 : edgeSignCheck 128 64 1 60 32 100 = true := by decide +kernel
theorem cell061 : edgeSignCheck 128 64 1 61 32 100 = true := by decide +kernel
theorem cell062 : edgeSignCheck 128 64 1 62 32 100 = true := by decide +kernel
theorem cell063 : edgeSignCheck 128 64 1 63 32 100 = true := by decide +kernel
theorem cell064 : edgeSignCheck 128 64 1 64 32 100 = true := by decide +kernel
theorem cell065 : edgeSignCheck 128 64 1 65 32 100 = true := by decide +kernel
theorem cell066 : edgeSignCheck 128 64 1 66 32 100 = true := by decide +kernel
theorem cell067 : edgeSignCheck 128 64 1 67 32 100 = true := by decide +kernel
theorem cell068 : edgeSignCheck 128 64 1 68 32 100 = true := by decide +kernel
theorem cell069 : edgeSignCheck 128 64 1 69 32 100 = true := by decide +kernel
theorem cell070 : edgeSignCheck 128 64 1 70 32 100 = true := by decide +kernel
theorem cell071 : edgeSignCheck 128 64 1 71 32 100 = true := by decide +kernel
theorem cell072 : edgeSignCheck 128 64 1 72 32 100 = true := by decide +kernel
theorem cell073 : edgeSignCheck 128 64 1 73 32 100 = true := by decide +kernel
theorem cell074 : edgeSignCheck 128 64 1 74 32 100 = true := by decide +kernel
theorem cell075 : edgeSignCheck 128 64 1 75 32 100 = true := by decide +kernel
theorem cell076 : edgeSignCheck 128 64 1 76 32 100 = true := by decide +kernel
theorem cell077 : edgeSignCheck 128 64 1 77 32 100 = true := by decide +kernel
theorem cell078 : edgeSignCheck 128 64 1 78 32 100 = true := by decide +kernel
theorem cell079 : edgeSignCheck 128 64 1 79 32 100 = true := by decide +kernel
theorem cell080 : edgeSignCheck 128 64 1 80 32 100 = true := by decide +kernel
theorem cell081 : edgeSignCheck 128 64 1 81 32 100 = true := by decide +kernel
theorem cell082 : edgeSignCheck 128 64 1 82 32 100 = true := by decide +kernel
theorem cell083 : edgeSignCheck 128 64 1 83 32 100 = true := by decide +kernel
theorem cell084 : edgeSignCheck 128 64 1 84 32 100 = true := by decide +kernel
theorem cell085 : edgeSignCheck 128 64 1 85 32 100 = true := by decide +kernel
theorem cell086 : edgeSignCheck 128 64 1 86 32 100 = true := by decide +kernel
theorem cell087 : edgeSignCheck 128 64 1 87 32 100 = true := by decide +kernel
theorem cell088 : edgeSignCheck 128 64 1 88 32 100 = true := by decide +kernel
theorem cell089 : edgeSignCheck 128 64 1 89 32 100 = true := by decide +kernel
theorem cell090 : edgeSignCheck 128 64 1 90 32 100 = true := by decide +kernel
theorem cell091 : edgeSignCheck 128 64 1 91 32 100 = true := by decide +kernel
theorem cell092 : edgeSignCheck 128 64 1 92 32 100 = true := by decide +kernel
theorem cell093 : edgeSignCheck 128 64 1 93 32 100 = true := by decide +kernel
theorem cell094 : edgeSignCheck 128 64 1 94 32 100 = true := by decide +kernel
theorem cell095 : edgeSignCheck 128 64 1 95 32 100 = true := by decide +kernel
theorem cell096 : edgeSignCheck 128 64 1 96 32 100 = true := by decide +kernel
theorem cell097 : edgeSignCheck 128 64 1 97 32 100 = true := by decide +kernel
theorem cell098 : edgeSignCheck 128 64 1 98 32 100 = true := by decide +kernel
theorem cell099 : edgeSignCheck 128 64 1 99 32 100 = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull.Kernel.Strip01
