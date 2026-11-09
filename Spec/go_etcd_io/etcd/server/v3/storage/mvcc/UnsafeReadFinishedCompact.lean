/-
`UnsafeReadFinishedCompact(tx)` (`store.go:22`). Internal: `restore`, `checkPrevCompactionCompleted`.
Reads `Meta`'s finished compaction key through any transaction seeing `D` (a read transaction's
`kbRead` or the batch's `kbLocked`: `rangeOk`); the value parses (`metaOk`: the image's; else
`BytesToRev` panics). The value's bytes are lent against a share `L p` of the transaction's
liveness (`rangeLent`) and given back once parsed, before the return. Not on a concurrent read
transaction (single-key, `KeyData.linger`: mvcc never reads `Meta` through one).

**Changes** from `specs-ref`'s file: over the storage contract's `rangeOk` in place of
`metaReadSpecR`/`rdCap`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `UnsafeReadFinishedCompact(tx)`: the finished compaction key's main revision and whether it is
there (`metaRev D.fin`). -/
def UnsafeReadFinishedCompact.spec : Prop :=
  ∀ (t : GoInterfaceOk) (R : IProp GF) (L : Qp → IProp GF) (p : Qp) (D : KeyData) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ schemaVars ∗
      rangeOk t R L D false (if b then KeyData.range else KeyData.rtRange) ∗ R ∗ L p ∗ ⌜D.metaMade = true ∧ metaOk D.fin⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadFinishedCompact))
      (Val #(GoInterface.ok t)))
  {{ (x : w64) (found : Bool), RET (PairV #x #found); R ∗ L p ∗ ⌜(x, found) = metaRev D.fin⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
