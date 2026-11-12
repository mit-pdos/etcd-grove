/-
**A writing transaction that passes the gRPC layer's checks has the shape its apply needs**
(D19c, option (a), 2026-10-18; `notes/decisions.md`, D19c). Lean-first (no Rocq counterpart).

The apply thread's premise on a transaction (`txn.TxnPre`) is, but for its size clauses, its shape
(`txn.txnShape`: every `IgnoreValue` put finds its key unless the key was missing at the start;
every get at revision `0`, with a valid sort target, its sort not cut by the limit). The proposer
carries it (`txnPermit`), and the gRPC layer gives it (`txnShape_of_check`): `checkRequestOp`
(`opsCheck`: keys not empty, sort targets valid) and `checkIntervals` (`intervalsOk`: no put of a
key a delete of the transaction removes, by `check_gives_nodup`), with the wire's no-`[0]` range
end (`txnNoZeroEnd`, so no from-key delete: `issues/etcd-txn-delete-then-ignore-put.md`), the
plainness the server's permit takes (`txn.txnPlain`: gets at revision `0`), and two client
premises: no nested transaction puts a key a later sibling deletes (`ReqOp.siblingSafeL`,
`check_gives_nodup`'s; stronger than the `IgnoreValue` puts need, which only meet earlier
deletes: `issues/etcd-txn-check-intervals-sibling.md`), and no get, at any depth, is a sort cut by
a limit (`txn.OpsNoCut`, `issues/etcd-range-sort-none-limit.md`; until D19c a read-only
transaction's premise only, `txnInModel`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckNodup
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckPure
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WorkloadDefs
public import Spec.google_golang_org.protobuf.proto.MarshalIRR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

/-- A range passing `checkRangeRequest` has a valid sort target. -/
theorem validSortTarget_of_rangeCheck (o : OpFull) (h : rangeCheck o = none) :
    txn.validSortTarget o := by
  unfold rangeCheck at h
  unfold txn.validSortTarget
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i h3
  simp only [sortTargetKnown, Bool.not_eq_true', decide_eq_false_iff_not] at h3
  exact Classical.not_not.1 h3

mutual
/-- **Every get of a checked plain operation**, at any depth, is within the model, given that
none is a sort cut by the limit. -/
theorem opGets_of_check : ∀ (n : Int) (u : ReqOp) (t : TxnOp), opCheck n u = none →
    ReqOp.toTxnOp u = some t → txn.opPlain t → txn.OpNoCut t → txn.OpGetsOk t
  | _, .range o, t, hc, ht, hp, hn => by
    simp only [ReqOp.toTxnOp, Option.some.injEq] at ht; subst ht
    exact ⟨hp, validSortTarget_of_rangeCheck o hc, hn⟩
  | _, .put o, t, _, ht, _, _ => by
    simp only [ReqOp.toTxnOp, Option.some.injEq] at ht; subst ht
    unfold txn.putTxnOp; split <;> (try split) <;> trivial
  | _, .delete o, t, _, ht, _, _ => by
    simp only [ReqOp.toTxnOp, Option.some.injEq] at ht; subst ht; trivial
  | n, .txn cs ts es, t, hc, ht, hp, hn => by
    simp only [ReqOp.toTxnOp] at ht
    split at ht
    · rename_i ts' es' hts hes
      simp only [Option.some.injEq] at ht; subst ht
      simp only [opCheck] at hc
      split at hc
      · cases hc
      split at hc
      · cases hc
      split at hc
      · cases hc
      rename_i hts0
      simp only [txn.opPlain] at hp
      simp only [txn.OpNoCut] at hn
      exact ⟨opsGets_of_check _ ts ts' hts0 hts hp.1 hn.1,
        opsGets_of_check _ es es' hc hes hp.2 hn.2⟩
    · cases ht
  | _, .empty, _, hc, _, _, _ => by simp [opCheck] at hc

theorem opsGets_of_check : ∀ (n : Int) (us : List ReqOp) (ts : List TxnOp), opsCheck n us = none →
    ReqOp.toTxnOps us = some ts → txn.opsPlain ts → txn.OpsNoCut ts → txn.OpsGetsOk ts
  | _, [], ts, _, ht, _, _ => by
    simp only [ReqOp.toTxnOps, Option.some.injEq] at ht; subst ht; trivial
  | n, u :: us, ts, hc, ht, hp, hn => by
    simp only [ReqOp.toTxnOps] at ht
    split at ht
    · rename_i t ts' h1 h2
      simp only [Option.some.injEq] at ht; subst ht
      simp only [opsCheck] at hc
      split at hc
      · cases hc
      rename_i hu
      exact ⟨opGets_of_check n u t hu h1 hp.1 hn.1, opsGets_of_check n us ts' hc h2 hp.2 hn.2⟩
    · cases ht
end

mutual
/-- No from-key delete, at any depth, in operations whose model has no `[0]` range end. -/
theorem noFromKeyDel_of : ∀ (u : ReqOp) (t : TxnOp), ReqOp.toTxnOp u = some t →
    txnOpNoZeroEnd t → ReqOp.noFromKeyDel u
  | .range _, _, _, _ => trivial
  | .put _, _, _, _ => trivial
  | .delete o, t, ht, hz => by
    simp only [ReqOp.toTxnOp, Option.some.injEq] at ht; subst ht; exact hz
  | .txn cs ts es, t, ht, hz => by
    simp only [ReqOp.toTxnOp] at ht
    split at ht
    · rename_i ts' es' hts hes
      simp only [Option.some.injEq] at ht; subst ht
      exact ⟨noFromKeyDelL_of ts ts' hts hz.2.1, noFromKeyDelL_of es es' hes hz.2.2⟩
    · cases ht
  | .empty, _, ht, _ => by simp [ReqOp.toTxnOp] at ht

theorem noFromKeyDelL_of : ∀ (us : List ReqOp) (ts : List TxnOp), ReqOp.toTxnOps us = some ts →
    txnOpsNoZeroEnd ts → ReqOp.noFromKeyDelL us
  | [], _, _, _ => trivial
  | u :: us, ts, ht, hz => by
    simp only [ReqOp.toTxnOps] at ht
    split at ht
    · rename_i t ts' h1 h2
      simp only [Option.some.injEq] at ht; subst ht
      exact ⟨noFromKeyDel_of u t h1 hz.1, noFromKeyDelL_of us ts' h2 hz.2⟩
    · cases ht
end

/-- **One branch's shape** from its checks (see the file header). -/
theorem branchIG_of_check (n : Int) (ops : List ReqOp) (tops : List TxnOp) (s0 : List EtcdKv)
    (r : w64) (hs : s0.Pairwise etcdKvLess) (htx : ReqOp.toTxnOps ops = some tops)
    (hck : opsCheck n ops = none) (hfk : ReqOp.noFromKeyDelL ops) (hsib : ReqOp.siblingSafeL ops)
    (hiv : intervalsOk ops) (hg : txn.OpsGetsOk tops) :
    txn.OpsIG true s0 r s0 tops := by
  have hnd := check_gives_nodup n ops tops s0 s0 r htx hck hfk hsib hiv
  exact txn.opsIG_of s0 r tops s0 hs hg fun k hk => ⟨hnd.2 k hk, id⟩

/-- **A checked writing transaction has the shape its apply needs** (see the file header): its
branches' models `ts'`, `es'`. -/
theorem txnShape_of_check (n : Int) (cs : List CmpModel) (ts es : List ReqOp)
    (ts' es' : List TxnOp) (hts : ReqOp.toTxnOps ts = some ts') (hes : ReqOp.toTxnOps es = some es')
    (hck : txnReqOk n cs ts es) (hivT : intervalsOk ts) (hivE : intervalsOk es)
    (hz : txnOpsNoZeroEnd ts' ∧ txnOpsNoZeroEnd es')
    (hsib : ReqOp.siblingSafeL ts ∧ ReqOp.siblingSafeL es)
    (hpl : txn.txnPlain { cmps := cs, thenOps := ts', elseOps := es' })
    (hnc : txn.OpsNoCut ts' ∧ txn.OpsNoCut es') :
    txn.txnShape { cmps := cs, thenOps := ts', elseOps := es' } := by
  have hok := (txnCheck_ok_iff n cs ts es).1 hck
  have hcT : opsCheck (n - txnWidth cs ts es) ts = none := (opsCheck_none_iff _ ts).2 hok.2.2.1
  have hcE : opsCheck (n - txnWidth cs ts es) es = none := (opsCheck_none_iff _ es).2 hok.2.2.2
  intro s0 r hs
  unfold TxnModel.branch
  split
  · exact branchIG_of_check _ ts ts' s0 r hs hts hcT (noFromKeyDelL_of ts ts' hts hz.1) hsib.1
      hivT (opsGets_of_check _ ts ts' hcT hts hpl.1 hnc.1)
  · exact branchIG_of_check _ es es' s0 r hs hes hcE (noFromKeyDelL_of es es' hes hz.2) hsib.2
      hivE (opsGets_of_check _ es es' hcE hes hpl.2 hnc.2)

end v3rpc
end EtcdGrove
end Perennial
