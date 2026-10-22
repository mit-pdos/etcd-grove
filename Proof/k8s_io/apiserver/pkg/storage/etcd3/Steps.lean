/-
Lean-first (no Rocq counterpart).

# The store's transactions are the model's steps (`StepOk`, D30h, `notes/k8s-etcd3-plan.md` phase 4)

On etcd's states that are the store's, each transaction the store sends moves the model as its
operation (`Model.lean`'s `absK_*` at the level of linkv's model, lifted to etcd's `kvOpStep` by
linkv's `absSt_kvOpStep`), and keeps the store's states (`KWf_*`, sortedness by
`kvOpStep_sorted`):

- `stepOk_create`: `Create`'s `OptimisticPut(key, value, 0)` of a value that reads as the object,
  canonically, is the model's `create`.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Updates
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.TxnModelKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section steps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj]

/-- `OptimisticPut`'s transaction is linkv's `putTxn` on the wire. -/
theorem kvOpStep_optPut (k v : GoString) (rev : w64) (g : Bool) (σ : KVState) :
    kvOpStep (.txn (kubernetes.optPutTxn k v rev g)) σ =
      kvOpStep (linkv.opOf [] [] (putTxn k v rev g)) σ := by
  cases g <;> rfl

/-- **`Create`'s transaction is the model's `create`.** -/
theorem stepOk_create (c : StoreCfg GF Obj) (pk v : GoString) (o : Obj) (hpk : c.pfx <+: pk)
    (hv : c.S.dec v = some (o, true)) :
    StepOk c (.txn (kubernetes.optPutTxn pk v (W64 0) false))
      (fun s => (s.create (E := Empty) pk o 0).1) := by
  intro σ hwf hb
  have hs := hwf.1
  have habs := linkv.absSt_kvOpStep [] [] [] σ hs (putTxn pk v (W64 0) false)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact linkv.kvOpStep_sorted _ σ hs
  · rw [kvOpStep_optPut, habs]
    exact KWf_putTxn c.S.dec c.pfx [] (linkv.absSt σ) hwf.2 hb pk v (W64 0) false
      (fun _ => by rw [hv]; rfl)
  · unfold StoreCfg.abs
    rw [kvOpStep_optPut, habs]
    exact (absK_create c.S.dec c.pfx [] (linkv.absSt σ) hwf.2 pk v o hpk hv).1

/-- **`Create`'s answer** at a state of the store: the object at the transaction's revision if it
succeeded (the key was absent), the key existing otherwise. -/
theorem create_out (c : StoreCfg GF Obj) (σ : KVState) (hwf : kvWf c σ) (pk v : GoString) (o : Obj)
    (hpk : c.pfx <+: pk) (hv : c.S.dec v = some (o, true)) :
    ((c.abs σ).create (E := Empty) pk o 0).2 =
      if (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (kubernetes.optPutTxn pk v (W64 0) false)).1 then
        .obj o (kvOpStep (.txn (kubernetes.optPutTxn pk v (W64 0) false)) σ).rev
      else .err (.keyExists pk) := by
  have hc := (absK_create (E := Empty) c.S.dec c.pfx [] (linkv.absSt σ) hwf.2 pk v o hpk hv).2
  have hout := linkv.mStep_txn_out [] [] [] σ hwf.1 [.mod pk (W64 0)] [.put pk v] []
  have heq : putTxn pk v (W64 0) false = .txn [.mod pk (W64 0)] [.put pk v] [] := rfl
  rw [heq, hout] at hc
  unfold StoreCfg.abs
  rw [kvOpStep_optPut, heq]
  have ht : kubernetes.optPutTxn pk v (W64 0) false =
      linkv.txnOf [.mod pk (W64 0)] [.put pk v] [] := rfl
  rw [ht]
  cases hok : (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
      (linkv.txnOf [.mod pk (W64 0)] [.put pk v] [])).1
  · rw [hok] at hc
    exact hc
  · rw [hok] at hc
    exact hc

end steps

end k8s
end EtcdGrove
end Perennial
