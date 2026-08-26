import LeanCipher.BalancedEightCertificates

namespace LeanCipher.BalancedEightCertificates

theorem weight63_tables_generated_by_executable_enumerator :
    canonicalEntries (generatedEntriesFor 63) =
      canonicalEntries (declaredEntriesFor 63) := by
  native_decide

end LeanCipher.BalancedEightCertificates
