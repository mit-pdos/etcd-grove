/-
`newOwnerRecord(ownerUID)` (`consistency.go:172`): a new empty record. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.consistency.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI k8s_io.client_go.util.consistency

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

/-- `newOwnerRecord(uid)`: a fresh `*ownerRecord` with `uid`, an unlocked lock and an empty
`versions` map. -/
abbrev newOwnerRecord.spec : Prop :=
  ∀ (uid : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency }}
    (App (Val (@! newOwnerRecord)) (Val #uid))
  {{ (r : Loc), RET #r; ∃ vm : Loc, ⌜r ≠ null⌝ ∗
      structFieldRef ownerRecord go!"ownerUID" r ↦ uid ∗
      structFieldRef ownerRecord go!"versionsLock" r ↦ (zero_val _root_.Perennial.sync.Mutex) ∗
      structFieldRef ownerRecord go!"versions" r ↦ vm ∗ vm ↦$ (∅ : Vs) }}

end spec

end consistency
end EtcdGrove
end Perennial
