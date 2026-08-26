import LeanCipher.BalancedEightEnumeration59
import LeanCipher.BalancedEightEnumeration61
import LeanCipher.BalancedEightEnumeration63

namespace LeanCipher.BalancedEightCertificates

theorem all_local_tables_generated_by_executable_enumerator :
    canonicalEntries (generatedEntriesFor 59) = canonicalEntries (declaredEntriesFor 59) ∧
    canonicalEntries (generatedEntriesFor 61) = canonicalEntries (declaredEntriesFor 61) ∧
    canonicalEntries (generatedEntriesFor 63) = canonicalEntries (declaredEntriesFor 63) :=
  ⟨weight59_tables_generated_by_executable_enumerator,
    weight61_tables_generated_by_executable_enumerator,
    weight63_tables_generated_by_executable_enumerator⟩

end LeanCipher.BalancedEightCertificates
