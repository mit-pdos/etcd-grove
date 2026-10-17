/-
`sharedBoltTx.bucket` (the backend, `read_tx.go`; added by etcd#22215). `st.bucket(bucketType)`: the bucket of the interval's bbolt read transaction, from the buckets map (under `txMu.RLock`), else from the transaction and cached (under `txMu.Lock`): a handle of the bucket in its snapshot `D`, or nil if `D` has none (`bktFact`).
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `st.bucket(bucketType)`: the bucket of the interval's bbolt read transaction, from the buckets map (under `txMu.RLock`), else from the transaction and cached (under `txMu.Lock`): a handle of the bucket in its snapshot `D`, or nil if `D` has none (`bktFact`). -/
abbrev backend.sharedBoltTx.bucket.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (st : Loc) (dq : DFrac) (rtx : Loc) (D : Data) (q : Qp)
    (bk : GoInterface) (bi : BucketInfo),
  P.has bi →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ stRd γ P st dq rtx D q ∗ isBucket bk bi }}
    (App (Val (st @!! go.GoType.PointerType sharedBoltTx.ty @!! go!"bucket")) (Val #bk))
  {{ (bkv : Loc), RET #bkv; stRd γ P st dq rtx D q ∗ bktFact rtx D bi.name bkv }}

end spec

end EtcdGrove
end Perennial
