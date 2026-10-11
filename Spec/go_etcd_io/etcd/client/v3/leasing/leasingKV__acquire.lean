/-
`lkv.acquire(ctx, key, op)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **What `acquire` returns** for the key `key` and the get `o` (of `key` alone, at the latest
revision): the transaction at a revision `r ≥ lo` (reached; etcd's state at `r` is `s`), its
header, its `Succeeded` `ok` (owned: `acquire` rewrote it), its first response the get's (owned,
`rangeRespOwn`, on `s`); if `ok`, the lease key `pfx ++ key` is present at `r` with a lease `id`
of this client's sessions (`Then` put it, or it already had it), created at or before `r`, and
the entries map was made and a session set. -/
def acquireResult (γ : LeasingNames) (pfx key : GoString) (lo : w64) (o : OpFull) (resp : Loc) :
    IProp GF :=
  iprop(∃ (r : w64) (s : List EtcdKv) (hdr : Loc) (hm : HdrM) (rsl : GoSlice) (p0 w rr : Loc)
      (ps : List Loc) (n : Nat) (ok : Bool),
    ⌜hm.revision = r ∧ sint.Z lo ≤ sint.Z r ∧ 0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 ∧
      EtcdStateWf [] s⌝ ∗ etcdReached r ∗ □ etcdState r [] s ∗
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗ hdrFull hdr hm ∗
    structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦ ok ∗
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ rsl ∗ rsl ↦*□ (p0 :: ps) ∗
    ⌜p0 ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseOp go!"Response" p0 ↦□
      interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w ∗
    structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ rr ∗
    ⌜rr ≠ null⌝ ∗ rangeRespOwn rr o (rangeSel s o) n ∗
    (if ok then iprop(∃ (id : w64) (lv : EtcdKv),
        ⌜kvOf s (pfx ++ key) = some lv ∧ lv.lease = id ∧ sint.Z lv.createRev ≤ sint.Z r⌝ ∗
        leaseCacheReady γ.lc ∗ sessionReady γ)
     else iprop(True)))

/-- **`lkv.acquire(ctx, key, op)`** for a get `op` (`o`) of `key` alone: until the context is done
(and the session is ready), commits "if the lease key is absent and `key` has no lease, `op` and
put the lease key with this session's lease, else `op` and get the lease key"; a failed
transaction succeeded if the lease key already has this session's lease. Returns an error, or
`acquireResult`. -/
abbrev leasingKV.acquire.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (key : GoString) (opv : go_etcd_io.etcd.client.v3.Op)
    (o : OpFull) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ context.isContext ctx cs ∗ opFullAt opv o ∗ etcdReached lo ∗
      ⌜txnOpOf o = some (.get o) ∧ o.key = key ∧ o.base.rangeEnd = []⌝ }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"acquire")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opv))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); lkvReader lkv γ pfx ∗
      (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ acquireResult γ pfx key lo o resp)) }}

end spec

end leasing
end EtcdGrove
end Perennial
