/-
bbolt's `discardLogger` (U11c): the no-op `*nopLogger` bbolt's package initializer stores in it
(`bboltRootInit_discard`) is a `boltLogger` (its methods return at once) and `logPtrTyped`.
`Inv/Bolt.discardLogger_boltLogger`'s stub is stated without the package's `Assumptions`, which
give `*nopLogger`'s methods (`MethodUnfold`): unprovable as stated; this is it with them.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Bolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section s
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
/-- **`discardLogger` holds a `boltLogger`** (`Inv/Bolt.discardLogger_boltLogger` with the
package's `Assumptions`). -/
theorem discardLogger_boltLogger' :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ⊢
      ∃ lg, globalAddr discardLogger ↦□ lg ∗ boltLogger lg := by
  iintro #Hpkg
  icases bboltRootInit_discard $$ Hpkg with ⟨%l, #Hd⟩
  iexists _
  iframe Hd
  unfold boltLogger
  simp only [interface.mkOk]
  imodintro
  iintro %m %fmtS %vs %args %xs %dq %R %hm
  obtain ⟨hm, -, -⟩ := hm
  simp only [boltLogMethods, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  all_goals
    wp_start as ⟨Ha, -, HR⟩
    wp_auto
    iapply HΦ; iframe

omit hos in
/-- `discardLogger`'s value, a `*nopLogger`, is `logPtrTyped`. -/
theorem discardLogger_logPtrTyped :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ⊢
      ∃ lg, globalAddr discardLogger ↦□ lg ∗ boltLogger lg ∗ ⌜logPtrTyped lg⌝ := by
  iintro #Hpkg
  ihave #Hb := discardLogger_boltLogger' $$ Hpkg
  icases bboltRootInit_discard $$ Hpkg with ⟨%l, #Hd⟩
  icases Hb with ⟨%lg, #Hd', #Hb⟩
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ Hd Hd'
  subst Heq
  iexists _; iframe Hd Hb
  ipureintro
  intro ii hii T _
  cases hii
  exact ⟨l, rfl⟩

end s

end bbolt
end EtcdGrove
end Perennial
