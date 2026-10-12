/-
The apply package's lemmas on the KV at the sole writer (`server/v3/etcdserver/apply`): the
leases of the state stay known across the backend applier's writes (a put, a delete, a
revocation's deletions). Lean-first (no Rocq counterpart); shared by the backend applier's
proofs (`applierV3backend__Put.lean`, ...).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriterKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode

/-- Deletions keep a sub-list of the state. -/
theorem applyChanges_dels_mem (r : w64) :
    ∀ (pend : List mvcc.Change) (s : List EtcdKv), (∀ c ∈ pend, c.isDel = true) →
      ∀ v ∈ mvcc.applyChanges r s pend, v ∈ s
  | [], s, _, v, hv => by simpa [mvcc.applyChanges] using hv
  | c :: cs, s, h, v, hv => by
    have hc := h c (List.mem_cons_self ..)
    have hcs : ∀ c' ∈ cs, c'.isDel = true := fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    simp only [mvcc.applyChanges, List.foldl_cons] at hv
    have := applyChanges_dels_mem r cs (mvcc.applyChange r s c) hcs v hv
    cases c with
    | put k v' l => simp [mvcc.Change.isDel] at hc
    | del k => simp only [mvcc.applyChange] at this; exact (List.mem_filter.1 this).1

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **Deletions committed keep the leases known** (a revocation's). -/
theorem leasesKnown_commit_dels (γl : GName) (log : mvcc.Log) (pend : List mvcc.Change)
    (h : ∀ c ∈ pend, c.isDel = true) :
    txn.leasesKnown (GF := GF) γl (mvcc.stateAfter log) ⊢
      txn.leasesKnown γl (mvcc.stateAfter (mvcc.commitLog log pend)) := by
  rw [txn.stateAfter_commitLog]
  apply txn.leasesKnown_sub
  exact applyChanges_dels_mem _ pend _ h

/-- **A delete committed keeps the leases known.** -/
theorem leasesKnown_commit_delete (γl : GName) (log : mvcc.Log) (o : OpFull) :
    txn.leasesKnown (GF := GF) γl (mvcc.stateAfter log) ⊢
      txn.leasesKnown γl
        (mvcc.stateAfter (mvcc.commitLog log (txn.delChanges (mvcc.stateAfter log) o))) := by
  rw [txn.stateAfter_commitLog]
  exact txn.leasesKnown_delete γl _ _ o

/-- **A put's kept lease is known** (`IgnoreLease`: the previous key-value's, of the state). -/
theorem leaseOk_ignore (γl : GName) (s : List EtcdKv) (o : OpFull) :
    txn.leasesKnown (GF := GF) γl s ⊢
      □ (⌜o.ignoreLease = true⌝ -∗ txn.leaseOk γl (txn.putLeaseOf o (mvcc.findKey o.key s))) := by
  iintro #Hk
  imodintro
  iintro %hl
  unfold txn.putLeaseOf
  simp only [hl, ↓reduceIte]
  cases hf : mvcc.findKey o.key s with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    unfold txn.leaseOk; ileft; ipureintro; rfl
  | some v =>
    simp only [Option.map_some, Option.getD_some]
    iunfold txn.leasesKnown at Hk
    iapply txn.leasesOk_mem γl _ _ ?_ $$ Hk
    exact List.mem_map_of_mem (List.mem_of_find?_eq_some hf)

/-- **A put committed keeps the leases known**, its own lease known. -/
theorem leasesKnown_putChange (γl : GName) (log : mvcc.Log) (o : OpFull) (pv : Option EtcdKv) :
    txn.leasesKnown (GF := GF) γl (mvcc.stateAfter log) ∗ txn.leaseOk γl (txn.putLeaseOf o pv) ⊢
      txn.leasesKnown γl (mvcc.stateAfter (log ++ [[txn.putChangeOf o pv]])) := by
  rw [txn.stateAfter_snoc]
  simp only [mvcc.applyChanges, List.foldl_cons, List.foldl_nil, txn.putChangeOf,
    mvcc.applyChange]
  exact txn.leasesKnown_put γl _ _ _ _ _

end lemmas

end apply
end EtcdGrove
end Perennial
