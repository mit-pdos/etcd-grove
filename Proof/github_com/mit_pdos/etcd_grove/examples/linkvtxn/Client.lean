/-
Lean-first (no Rocq counterpart).

# linkvtxn: the client's operations of the model's (linkv-txn stage F)

What `call`'s client calls send, as the client's models: a transaction operation `opOf` builds
(`clientOp`: `OpGet(k)`, `OpPut(k, v)`, `OpDelete(k)`), as `Then`/`Else` take it (`clientTOp`,
`txnOpOf_clientOp`) and as the server decodes it (`opWire_clientTOp`: the model's `linkv.tOpOf`);
the transaction the builder holds after `If`/`Then`/`Else` (`clientTxn`), whose wire model is the
model's (`txnWireOf_clientTxn`: `linkv.txnOf`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Enc
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

section client
variable [ext : FfiSyntax]

/-- **The `Op` `opOf` builds** for a model transaction operation. -/
def clientOp : linkv.MOp GoString GoString → OpFull
  | .get k => opGetModel k []
  | .put k v => opPutModel k v []
  | .del k => opDeleteModel k []

/-- The transaction operation it stands for (`txnOpOf`). -/
def clientTOp : linkv.MOp GoString GoString → TxnOp
  | .get k => .get (opGetModel k [])
  | .put k v => .put k v (W64 0)
  | .del k => .delete (opDeleteModel k [])

theorem txnOpOf_clientOp (m : linkv.MOp GoString GoString) :
    txnOpOf (clientOp m) = some (clientTOp m) := by
  cases m <;> rfl

theorem txnOpOf_clientOps (ms : List (linkv.MOp GoString GoString)) :
    (ms.map clientOp).map txnOpOf = (ms.map clientTOp).map some := by
  simp only [List.map_map]
  exact List.map_congr_left (fun m _ => txnOpOf_clientOp m)

theorem opWire_clientTOp (m : linkv.MOp GoString GoString) :
    opWire (clientTOp m) = linkv.tOpOf m := by
  cases m <;> simp only [clientTOp, opWire, linkv.tOpOf] <;> rfl

theorem clientOp_get_ok : ¬ opGetPanics [] := by
  simp [opGetPanics, opFold, OpFull.newOp]

theorem clientOp_put_ok (k v : GoString) : ¬ (opPutModel k v []).putPanics := by
  simp [opPutModel, opFold, OpFull.putInit, OpFull.newOp, OpFull.putPanics, OpModel.zero]

theorem clientOp_del_ok (k : GoString) : ¬ opDeletePanics k [] := by
  simp [opDeletePanics, opGetPanics, opDeleteModel, opFold, OpFull.deleteInit, OpFull.newOp,
    OpFull.deletePanics, OpModel.zero]

/-- **The transaction the builder holds** for the model's `cs`, `t`, `e`. -/
def clientTxn (cs : List (linkv.MCmp GoString GoString)) (t e : List (linkv.MOp GoString GoString)) :
    TxnModel :=
  { cmps := cs.map linkv.cmpOf, thenOps := t.map clientTOp, elseOps := e.map clientTOp }

theorem txnWireOf_clientTxn (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) :
    txnWireOf (clientTxn cs t e) = linkv.txnOf cs t e := by
  simp only [txnWireOf, clientTxn, linkv.txnOf, List.map_map]
  congr 1
  · exact List.map_congr_left (fun m _ => opWire_clientTOp m)
  · exact List.map_congr_left (fun m _ => opWire_clientTOp m)

end client

section iris
open Iris Iris.BI Iris.ProofMode

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- No options: the nil slice. -/
theorem optsAt_nil : ⊢ optsAt (GF := GF) slice.nil [] := by
  unfold optsAt
  iexists ([] : List GoFunc)
  isplitl
  · iapply ownSlice_nil
  isplitl
  · ipureintro; rfl
  imodintro
  iintro %i %f %g %Hf %Hg
  simp at Hf

end iris

end linkvtxn
end EtcdGrove
end Perennial
