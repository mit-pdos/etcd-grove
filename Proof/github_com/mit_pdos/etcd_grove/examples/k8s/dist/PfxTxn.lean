/- Lean-first (no Rocq counterpart).

# The k8s store's operations are local to `/registry/` (k8s-dist K8-6)

`KVPfxHist.pfxLocal_txn` takes, as a premise, that every change a Txn makes, in every state, is of a key
under the owned prefix. Here it is proved for the transactions a model input sends (`linkv.txnOf`: the
server's run of a branch changes only the branch's operations' keys, `srvOps_keys`), hence for the
k8s store's compare-put and compare-delete (`k8s.putTxn`/`k8s.delTxn`, else-get or nothing) of a key
under the prefix, and for every model input whose keys are under it (`pfxLocal_opOf`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPfxHist
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.TxnModelKV
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Model

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open go_etcd_io.etcd.server.v3.etcdserver mvcc linkv

/-- **The server's run of a model transaction's operations changes only their keys** (puts and
deletes alike), at every state. -/
theorem srvOps_keys (P : GoString → Prop) (s0 : List EtcdKv) (r : w64) :
    ∀ (ops : List (MOp GoString GoString)) (s : List EtcdKv), (∀ op ∈ ops, P op.key) →
      ∀ c ∈ (txn.srvOps s0 r s (ops.map tOpOf)).1, P c.key
  | [], _, _ => by simp [txn.srvOps]
  | op :: ops, s, hk => by
    simp only [List.map_cons, txn.srvOps_cons, List.mem_append]
    rintro c (hc | hc)
    · cases op with
      | get k => simp [tOpOf, txn.srvOp] at hc
      | put k v =>
        simp only [tOpOf, txn.srvOp, List.mem_singleton] at hc
        subst hc
        exact hk _ List.mem_cons_self
      | del k =>
        simp only [tOpOf, txn.srvOp, List.mem_map] at hc
        obtain ⟨w, hw, rfl⟩ := hc
        rw [rangeIn_delOp, List.mem_filter] at hw
        have hwk : w.key = k := by simpa using hw.2
        simp only [Change.key]
        rw [hwk]
        exact hk _ List.mem_cons_self
    · exact srvOps_keys P s0 r ops _ (fun o ho => hk o (List.mem_cons_of_mem _ ho)) c hc

/-- **A model transaction whose operations' keys are under `p` is local to `p`.** -/
theorem pfxLocal_txnOf (p : GoString) (cs : List (MCmp GoString GoString))
    (t e : List (MOp GoString GoString)) (h : ∀ op ∈ t ++ e, p <+: op.key) :
    PfxLocal p (kvOpStep (.txn (txnOf cs t e))) := by
  apply pfxLocal_txn
  intro σ c hc
  simp only [txn.srvRunTxn, txnOf_branch] at hc
  refine srvOps_keys (fun k => p <+: k) _ _ _ _ ?_ c hc
  intro op hop
  apply h
  cases txn.txnOk σ.kvs (txnOf cs t e) <;> simp_all

/-- A delete of one key under `p` is local to `p`. -/
theorem pfxLocal_delOp (p k : GoString) (hk : p <+: k) :
    PfxLocal p (kvOpStep (.deleteRange (delOp k))) := by
  apply pfxLocal_deleteRange
  intro s c hc
  simp only [txn.delChanges, List.mem_map] at hc
  obtain ⟨w, hw, rfl⟩ := hc
  rw [rangeIn_delOp, List.mem_filter] at hw
  have hwk : w.key = k := by simpa using hw.2
  simp only [Change.key]
  rw [hwk]
  exact hk

/-- **The k8s store's compare-put of a key under `p` (`OptimisticPut`) is local to `p`.** -/
theorem pfxLocal_putTxn (p lk le k v : GoString) (rev : w64) (g : Bool) (hk : p <+: k) :
    PfxLocal p (kvOpStep (opOf lk le (k8s.putTxn k v rev g))) := by
  simp only [k8s.putTxn, k8s.delTxn, opOf]
  apply pfxLocal_txnOf
  intro op hop
  cases g <;> simp_all [MOp.key]

/-- **The k8s store's compare-delete of a key under `p` (`OptimisticDelete`) is local to `p`.** -/
theorem pfxLocal_delTxn (p lk le k : GoString) (rev : w64) (g : Bool) (hk : p <+: k) :
    PfxLocal p (kvOpStep (opOf lk le (k8s.delTxn k rev g))) := by
  simp only [k8s.putTxn, k8s.delTxn, opOf]
  apply pfxLocal_txnOf
  intro op hop
  cases g <;> simp_all [MOp.key]

end etcd_dist
end EtcdGrove
end Perennial
