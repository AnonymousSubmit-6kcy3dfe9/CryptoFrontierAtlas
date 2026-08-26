import LeanCipher.BalancedEightCertificates

namespace LeanCipher.BalancedEightCertificates

theorem weight61_tables_generated_by_executable_enumerator :
    canonicalEntries (generatedEntriesFor 61) =
      canonicalEntries (declaredEntriesFor 61) := by
  native_decide

end LeanCipher.BalancedEightCertificates
