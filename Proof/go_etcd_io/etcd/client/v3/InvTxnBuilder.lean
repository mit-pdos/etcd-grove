/-
**The client's transaction builder over gRPC** (`client/v3/txn.go`; the vertical slice's unit V2,
2026-10-14): the state of a `*txn` (`kv.Txn`'s result) as a builder of the transaction model
(`TxnBuild`, the cache's `txnBuilderSpec`'s state). Lean-first (no Rocq counterpart).

**The builder** (`txnObjAt tp addr ci cd b`, owned by the caller: the builder is used by one
goroutine): the `*kv` it was made from (over a connection to the server at `addr`), its context (with
`ctxErrClient`, for `Commit`'s `ContextError`), its mutex (`txn.mu`: an invariant with nothing in
it; every method locks it), the flags `cif`, `cthen`, `celse` (`b`'s), and the comparisons and
operations so far as the requests `Commit` sends: `cmps` the `*pb.Compare`s of `b.model.cmps`
(clones of the caller's: `Cmp.Clone`), `sus` and `fas` the `*pb.RequestOp`s of the then- and
else-operations' wire models (`opWire`; `Op.toRequestOp`'s), each slice with its spare capacity
(the methods append to them). The operations are plain (gets, puts, deletes: `txnOpOf`'s, as
`txnBuilderSpec` takes them); `Commit` sends `txnWireOf b.model`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The `*txn` `tp` is a builder at the state `b`** (see the file header). -/
def txnObjAt (tp : Loc) (addr : GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) : IProp GF :=
  iprop(⌜tp ≠ null⌝ ∗ ∃ (api : Loc) (cosl csl ssl fsl : GoSlice) (cps sps fps : List Loc)
      (iw : Bool),
    structFieldRef go_etcd_io.etcd.client.v3.txn go!"kv" tp ↦□ api ∗ kvObjAt api addr ∗
    structFieldRef go_etcd_io.etcd.client.v3.txn go!"ctx" tp ↦□ GoInterface.ok ci ∗
    ctxOk ci cd ∗ ctxErrClient ci cd ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.client.v3.txn go!"mu" tp) iprop(True) ∗
    structFieldRef go_etcd_io.etcd.client.v3.txn go!"cif" tp ↦ b.cif ∗
    structFieldRef go_etcd_io.etcd.client.v3.txn go!"cthen" tp ↦ b.cthen ∗
    structFieldRef go_etcd_io.etcd.client.v3.txn go!"celse" tp ↦ b.celse ∗
    structFieldRef go_etcd_io.etcd.client.v3.txn go!"isWrite" tp ↦ iw ∗
    structFieldRef go_etcd_io.etcd.client.v3.txn go!"cmps" tp ↦ csl ∗ csl ↦* cps ∗
      ownSliceCap Loc csl (DFrac.own 1) ∗ comparesAt cps b.model.cmps ∗
    structFieldRef go_etcd_io.etcd.client.v3.txn go!"sus" tp ↦ ssl ∗ ssl ↦* sps ∗
      ownSliceCap Loc ssl (DFrac.own 1) ∗ reqOpsAt sps (b.model.thenOps.map opWire) ∗
    structFieldRef go_etcd_io.etcd.client.v3.txn go!"fas" tp ↦ fsl ∗ fsl ↦* fps ∗
      ownSliceCap Loc fsl (DFrac.own 1) ∗ reqOpsAt fps (b.model.elseOps.map opWire) ∗
    structFieldRef go_etcd_io.etcd.client.v3.txn go!"callOpts" tp ↦□ cosl ∗ callOptsAt cosl)

theorem comparesAt_nil : ⊢ comparesAt (GF := GF) [] [] := by
  unfold comparesAt
  iintro
  isplitl []
  · ipureintro; rfl
  imodintro
  iintro %i %p %m %h1 %h2
  simp at h1

theorem reqOpsAt_nil : ⊢ reqOpsAt (GF := GF) [] [] := by
  unfold reqOpsAt
  iintro
  isplitl []
  · ipureintro; rfl
  imodintro
  iintro %i %p %m %h1 %h2
  simp at h1

theorem comparesAt_snoc (ps : List Loc) (ms : List CmpModel) (p : Loc) (m : CmpModel) :
    comparesAt (GF := GF) ps ms ∗ ⌜p ≠ null⌝ ∗ compareAt p m ⊢ comparesAt (ps ++ [p]) (ms ++ [m]) := by
  unfold comparesAt
  iintro ⟨⟨%hl, #H⟩, %hp, #Hc⟩
  isplitl []
  · ipureintro; simp [hl]
  iapply pointwise_snoc (fun (p : Loc) (m : CmpModel) => iprop(⌜p ≠ null⌝ ∗ compareAt (GF := GF) p m))
    ps ms p m hl
  iframe #
  ipureintro; exact hp

theorem reqOpsAt_snoc (ps : List Loc) (ops : List TxnOp) (p : Loc) (op : TxnOp) :
    reqOpsAt (GF := GF) ps ops ∗ reqOpAt p op ⊢ reqOpsAt (ps ++ [p]) (ops ++ [op]) := by
  unfold reqOpsAt
  iintro ⟨⟨%hl, #H⟩, #Hc⟩
  isplitl []
  · ipureintro; simp [hl]
  iapply pointwise_snoc (fun (p : Loc) (op : TxnOp) => reqOpAt (GF := GF) p op) ps ops p op hl
  iframe #

end defs

end EtcdGrove
end Perennial
