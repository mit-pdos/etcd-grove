/-
## `(*batchTxBuffered).UnsafeForEach(bucket, visitor)` (promoted `batchTx.UnsafeForEach`, `batch_tx.go:248-258`): translated

**Users.** The schema's whole-bucket reads under the lock (4b: `MustUnsafeGetAllLeases`,
`lease.go:33`; membership's `membership.go:98, 111, 129, 138`; alarms; auth users),
`unsafeVerifyTxConsistency` (off). **Proof sketch.** bbolt's `Bucket.ForEach` on the write
transaction (a missing bucket: `nil`, nothing visited): the entries in key order, the visitor's
contract at each, stopping at its first error. **Changes.** New (no old spec). **Margin.** None.
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

/-- **`t.UnsafeForEach(bk, vis)`**: the visitor over the batch image's bucket in key order. -/
def batchTxBuffered.UnsafeForEach.spec : Prop :=
  ∀ (γ : BeNames) (q : Qp) (F : Fp) (S : Sess) (bk : GoInterface) (bi : BktInfo) (vis : GoFunc)
    (P : List (GoString × GoString) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beSess γ q F S ∗ bkt γ bk bi ∗ visitOk vis P ∗ P [] }}
    (App (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"UnsafeForEach")) (Val #bk)) (Val #vis))
  {{ (err : GoInterface), RET #err; beSess γ q F S ∗ ∃ l, ⌜btOrder (S.cur.ents bi.name) l⌝ ∗
      ((⌜err = interface.nil⌝ ∗ P l) ∨ (⌜err ≠ interface.nil⌝ ∗ ∃ j, P (l.take j))) }}

end spec

end Backend
end EtcdGrove
end Perennial
