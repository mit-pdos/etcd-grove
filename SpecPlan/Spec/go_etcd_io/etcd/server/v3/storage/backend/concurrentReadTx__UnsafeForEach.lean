/-
## `(*concurrentReadTx).UnsafeForEach(bucket, visitor)` (promoted `baseReadTx.UnsafeForEach`): translated

**Users.** mvcc's `hashByRev` (`hash.go:35`, a whole-`Key` scan on a `ConcurrentReadTx`).
**Proof sketch.** As `readTx.UnsafeForEach.spec` (the buffer's keys skipped in bbolt's pass: each key
once), over a possibly stale buffer copy (see `concurrentReadTx.UnsafeRange`): every entry of the
view, and maybe entries the last session deleted (`rdOrderL`). **Changes.** New; round 1 (T1): the
lingering entries; integration Y: the visitor's own error returned (`visitOk vis P E`), the bytes kept by the visitor and lent against a share of the transaction's liveness (`lentAll … -∗ beLive`), as `rangeRes` (I6's finding: 4b's `Schema.txRd` row needs both). **Margin.** The order is not stated.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

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

/-- **`rt.UnsafeForEach(bk, vis)`** on a concurrent read transaction: as on the shared one. -/
def concurrentReadTx.UnsafeForEach.spec : Prop :=
  ∀ (γ : BeNames) (l : Loc) (F : Fp) (V : Image) (bk : GoInterface) (bi : BktInfo) (vis : GoFunc)
    (P : List Lent → IProp GF) (E : List Lent → GoInterface → IProp GF) (pl : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beRd γ l F V ∗ beLive γ l pl ∗ bkt γ bk bi ∗ ⌜∀ x, F (.key bi.name x)⌝ ∗ visitOk vis P E ∗ P [] }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx.ty @!! go!"UnsafeForEach")) (Val #bk)) (Val #vis))
  {{ (err : GoInterface), RET #err; beRd γ l F V ∗ ∃ (r full : List Lent),
      ⌜rdOrderL (V.ents bi.name) (full.map Lent.ent) ∧ r <+: full⌝ ∗
      (lentAll r -∗ beLive γ l pl) ∗
      ((⌜err = interface.nil ∧ r = full⌝ ∗ P r) ∨ (⌜err ≠ interface.nil⌝ ∗ E r err)) }}

end spec

end Backend
end EtcdGrove
end Perennial
