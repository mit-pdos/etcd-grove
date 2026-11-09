/-
## `(*readTx).UnsafeForEach(bucket, visitor)` (promoted `baseReadTx.UnsafeForEach`, `read_tx.go:52-73`): translated

**Users.** The schema's whole-bucket reads on the read transaction (4b: alarms' `GetAllAlarms`,
auth's `UnsafeGetAllUsers`/`Roles`, membership's `MustReadMembersFromBackend`),
`unsafeVerifyTxConsistency` (off). **Proof sketch.** The buffer's keys collected (`getDups`);
bbolt's `ForEach` under `txMu` with the buffered keys skipped (a missing bucket: none); then the
buffer's entries; the visitor's contract at each, stopping at its first error. **Changes.** New
(no old spec). **Margin.** The split between the two runs is not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`rt.UnsafeForEach(bk, vis)`** on the shared read transaction: the visitor over its view of the
bucket, each entry once (`rdOrder`). -/
def readTx.UnsafeForEach.spec : Prop :=
  ∀ (γ : BeNames) (F : Fp) (V : Image) (bk : GoInterface) (bi : BktInfo) (vis : GoFunc)
    (P : List (GoString × GoString) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beRd γ (rtLoc γ) F V ∗ bucketOk bk bi ∗ ⌜∀ x, F (.key bi.name x)⌝ ∗ visitOk vis P ∗
      P [] }}
    (App (App (Val ((rtLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty @!! go!"UnsafeForEach")) (Val #bk)) (Val #vis))
  {{ (err : GoInterface), RET #err; beRd γ (rtLoc γ) F V ∗ ∃ l, ⌜rdOrder (V.ents bi.name) l⌝ ∗
      ((⌜err = interface.nil⌝ ∗ P l) ∨ (⌜err ≠ interface.nil⌝ ∗ ∃ j, P (l.take j))) }}

end spec

end Backend
end EtcdGrove
end Perennial
