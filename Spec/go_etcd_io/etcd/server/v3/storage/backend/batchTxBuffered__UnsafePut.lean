/-
`UnsafePut` (the backend). `t.UnsafePut(bucket, key, value)` under the lock: bbolt's writer and the write buffer get the
entry (a key of `1..MaxKeySize` bytes, read-only for good; a key not already put since the last
write-back; in a safe-range bucket a key above the writer's contents; a value above
`MaxValueSize` is fatal).
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

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

/-- `t.UnsafePut(bucket, key, value)` under the lock: bbolt's writer and the write buffer get the
entry (a key of `1..MaxKeySize` bytes, read-only for good: both keep the slices; a key not
already put since the last write-back, unless the read buffer has no such bucket or, in the
hook's window, an empty one (`wbDupOk`: the write-back's assumption, see
`issues/etcd-backend-duplicate-put-stale-read.md`); in a safe-range bucket, a key above the
writer's contents; a hook's own key (`P.hk`) with the client's half of them, `hkPut`, which it
gives back updated). A value above `MaxValueSize` makes bbolt fail and the backend's `lg.Fatal`
exit: the call does not return (`issues/etcd-backend-put-value-too-large-fatal.md`). -/
abbrev backend.batchTxBuffered.UnsafePut.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo) (key value : GoSlice) (kb vb : GoString),
  P.has bi → 0 < kb.length → kb.length ≤ maxKeySize →
  (kb ∉ (bkOf st.W.bks bi.id).map Prod.fst ∨ wbDupOk st bi.id) → sint.Z st.pend + 1 < 2 ^ 58 →
  (P.SB bi.name = true → ∀ kc vc, (bktOf st.S bi.name).lookup kc = some vc → strLt kc kb) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗ key ↦*□ kb ∗ value ↦*□ vb ∗ hkPut γ P bi.name kb st.S }}
    (App (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafePut")) (Val #bk)) (Val #key)) (Val #value))
  {{ RET #(); batchLocked γ P b (st.put bi kb vb false) ∗ hkPut γ P bi.name kb (st.put bi kb vb false).S }}

end spec

end EtcdGrove
end Perennial
