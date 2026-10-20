/-
**What a write's or a transaction's reply says of the state it linearized at** (linkv-txn stage
B3, 2026-10-20; `notes/linkv-txn-plan.md`): for each successful reply (`putReplied`,
`deleteReplied`, `txnReplied`), the state `σ` its client's update fired at (`Q σ`, or `□ Q σ` for
a read-only transaction's read update) and the reply's fields as functions of `σ`: a put's
revision (`σ`'s next) and previous key-value; a delete's count, revision (the state's after the
delete, `kvOpStep`'s) and previous key-values; a transaction's verdict, its branch's responses
and its revision (the state's after its writes, `KVState.commit`'s). As `client_get_value` and
`rangeReply_state` (`Results.lean`) for the reads. A writing transaction's ranges may be
header-only (`skip`: B1 is to exclude it). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Results

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
open mvcc

/-! ## The state of a log, by its length -/

/-- A log's state's next revision is its length. -/
theorem kvStateOf_rev_succ (l : mvcc.Log) (h : 2 ≤ l.length) :
    (kvStateOf l).rev + 1 = l.length := by
  unfold kvStateOf; simp only; omega

/-- **A write's revision is its state's after the changes** (`writeRev`, `KVState.commit`). -/
theorem kvStateOf_commit_rev (l : mvcc.Log) (cs : List mvcc.Change) (h : 2 ≤ l.length) :
    ((kvStateOf l).commit cs).rev = mvcc.writeRev l cs := by
  unfold KVState.commit mvcc.writeRev kvStateOf
  by_cases hc : cs = [] <;> simp only [hc, ↓reduceIte] <;> omega

section values
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What a successful `Put` returns**: its update `Q` fired at a state `σ` whose next
revision is the reply's and whose key-value of the key is the reply's previous one (if asked). -/
theorem client_put_value (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (cid mid : w64) (m : PutRespM) :
    putReplied E γr F o Q cid mid m ⊢
      ∃ σ : KVState, Q σ ∗ ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧
        m.prev = (if o.base.prevKV then mvcc.findKey o.key σ.kvs else none)⌝ := by
  iintro H
  unfold putReplied
  icases H with ⟨%hm, %x, %x', %l, %skip, %Hp, -, -, -, -, HQ⟩
  obtain ⟨-, hrev, -, -, hprev, -, hlen, -⟩ := Hp
  iexists kvStateOf x.log
  iframe HQ
  ipureintro
  refine ⟨?_, hprev⟩
  rw [hrev, kvStateOf_rev_succ _ hlen]

/-- **What a successful `DeleteRange` returns** (of a delete whose range end is not `[0]`, which
the wire keeps): its update `Q` fired at a state `σ` whose keys in the range are the reply's
count (and previous key-values, if asked), and whose state after the delete has the reply's
revision. -/
theorem client_delete_value (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (cid mid : w64) (m : DelRespM) (hz : o.base.rangeEnd ≠ [W8 0]) :
    deleteReplied E γr F o Q cid mid m ⊢
      ∃ σ : KVState, Q σ ∗ ⌜m.deleted = W64 ((rangeIn σ.kvs o).length : Int) ∧
        m.hdr.revision = W64 ((kvOpStep (.deleteRange o) σ).rev : Int) ∧
        m.prevs = (if o.base.prevKV then rangeIn σ.kvs o else [])⌝ := by
  iintro H
  unfold deleteReplied
  icases H with ⟨%hm, %rq', %op', %x, %x', %l, %skip, %Hp, -, -, -, -, HQ⟩
  obtain ⟨-, -, Hz, -, hrev, -, -, hdel, hprevs, -, hlen, -⟩ := Hp
  have hnz : irrNoZeroEnd (irrDeleteRange o) := by
    refine ⟨fun o' h => by simp [irrDeleteRange, apply.irrEmpty] at h, fun o' h => ?_,
      fun t h => by simp [irrDeleteRange, apply.irrEmpty] at h⟩
    simp only [irrDeleteRange, Option.some.injEq] at h
    subst h
    exact hz
  have hop : op' = o := Hz hnz
  subst hop
  iexists kvStateOf x.log
  iframe HQ
  ipureintro
  refine ⟨hdel, ?_, hprevs⟩
  rw [hrev]
  unfold kvOpStep
  rw [kvStateOf_commit_rev _ _ hlen]
  rfl

/-- **What a successful writing `Txn` returns** (of a transaction with no range end `[0]`, which
the wire keeps): its update `Q` fired at a state `σ`; the server's run of the transaction at `σ`
(at `σ`'s next revision) gives the reply's verdict and its branch's responses (header-only ranges
if `skip`), and the state after its changes has the reply's revision. -/
theorem client_txn_value (E : apply.AEnv GF) (γw γr : ReadNames) (c : w64) (F : mvcc.Log)
    (t : TxnModel) (Q : KVState → IProp GF) (cid mid : w64) (m : TxnRespM)
    (hro : txn.txnReadonly t = false) (hnz : irrNoZeroEnd (irrTxn t)) :
    txnReplied E γw γr c F t Q cid mid m ⊢
      ∃ (σ : KVState) (skip : Bool), Q σ ∗
        ⌜m.succeeded = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).1 ∧
          opRespsRel skip (t.branch m.succeeded)
            (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.2 m.resps ∧
          m.hdr.revision =
            W64 ((σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.1).rev :
              Int)⌝ := by
  iintro H
  unfold txnReplied
  simp only [hro, Bool.false_eq_true, ↓reduceIte]
  icases H with ⟨%hm, %rq', %t', %x, %x', %l, %skip, %Hp, -, -, -, -, HQ⟩
  obtain ⟨-, -, Hz, -, hrev, -, -, -, hlen, -, hok, hrel⟩ := Hp
  have ht : t' = t := Hz hnz
  subst ht
  have hr : ((kvStateOf x.log).rev + 1 : Nat) = x.log.length := kvStateOf_rev_succ _ hlen
  iexists kvStateOf x.log, skip
  iframe HQ
  ipureintro
  have hs : (kvStateOf x.log).kvs = mvcc.stateAfter x.log := rfl
  rw [hr, hs]
  refine ⟨hok, hrel, ?_⟩
  rw [hrev, ← hs, kvStateOf_commit_rev _ _ hlen, hs]

/-- **What a successful linearizable read-only `Txn` returns**: its read update `Q` fired at a
state `σ`; the server's run of the transaction at `σ` gives the reply's verdict and its branch's
responses (ranges executed), and `σ`'s revision is the reply's. -/
theorem client_txn_value_ro (E : apply.AEnv GF) (γw γr : ReadNames) (c : w64) (F : mvcc.Log)
    (t : TxnModel) (Q : KVState → IProp GF) (cid mid : w64) (m : TxnRespM)
    (hro : txn.txnReadonly t = true) (hser : txn.txnSerializable t = false) :
    txnReplied E γw γr c F t Q cid mid m ⊢
      ∃ σ : KVState, □ Q σ ∗
        ⌜m.succeeded = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).1 ∧
          opRespsRel false (t.branch m.succeeded)
            (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.2 m.resps ∧
          m.hdr.revision = W64 (σ.rev : Int)⌝ := by
  iintro H
  unfold txnReplied
  simp only [hro, hser, Bool.false_eq_true, ↓reduceIte]
  icases H with ⟨%log, -, -, %Hp, -, #HQ⟩
  obtain ⟨hlen, -, -, hrev, -, -, hok, hrel⟩ := Hp
  have hr : ((kvStateOf log).rev + 1 : Nat) = log.length := kvStateOf_rev_succ _ hlen
  iexists kvStateOf log
  iframe HQ
  ipureintro
  have hs : (kvStateOf log).kvs = mvcc.stateAfter log := rfl
  rw [hr, hs]
  refine ⟨hok, hrel, ?_⟩
  rw [hrev]
  unfold kvStateOf
  simp only
  congr 1
  omega

end values

end client
end EtcdGrove
end Perennial
