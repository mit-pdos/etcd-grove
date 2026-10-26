/-
**A client of etcd's KV meets the recipes' transaction contract** (D48, 2026-10-26). Lean-first,
no Rocq counterpart.

`isEtcdTxnKVTodo_of_km`: `kv.Txn(context.TODO())` on a `*kv` of etcd's KV `γ.kv` (`isKv`, writes
delivered at most once), with the adapter's invariant (`kmInv γ`, `EtcdModelKV.lean`), returns a
builder whose `If`, `Then`, `Else` are the client's (`txn.If`, ...) and whose `Commit`, for an
`exactGets` transaction under `pfx`, returns `txnCommitResultTok` at the adapter's model
(`etcdModelOfKV γ`). The call is `txn.Commit.spec`'s with the adapter's update after the floor the
caller knows (`km_reached_lb`): a linearizable read-only transaction's read update
(`km_read_au`), a writing one's update fired once (`km_write_au`, its token the revision's). The
reply's state `σ`, a well-formed log's (`kvLogOk`), is one the client saw; its log is the old
proof's (`ServerKVTxn.lean`), whose pure lemmas carry over.

Premises beyond the get bridge's (`KMGet.lean`):
* `kmReachedAt γ (W64 1)`: the client saw a state of revision `1` or more. The contract's revision
  is positive (`0 < r`); etcd's starts at `1`, but the KV state's model starts anywhere, so a
  read at revision `0` would break it.
* `kmTxnUncoveredTodo api γ`: the transactions no update of the spec covers. A read-only
  serializable transaction fires no update, so the adapter learns nothing of the state it read;
  a writing transaction with a lease or an `IgnoreValue` put (`¬ TxnModel.kmFree`) is outside the
  spec (`txnPlain`: no lease) or may fail `checkTxn` (`PathsIgnOk`), where the spec's step is the
  identity but its reply's revision the run's. The recipes commit neither.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ServerKVTxn
public import Proof.go_etcd_io.etcd.client.v3.EtcdModelKV
public import Proof.go_etcd_io.etcd.client.v3.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## Pure lemmas -/

/-- An operation the spec's write update covers, its `checkTxn` passing: no lease, no
`IgnoreLease`, no `IgnoreValue`. -/
def TxnOp.kmFree : TxnOp → Prop
  | .put _ _ l => l = W64 0
  | .putIgnVal _ _ => False
  | .putKeep _ _ => False
  | _ => True

/-- A transaction of `kmFree` operations (both branches). -/
def TxnModel.kmFree (t : TxnModel) : Prop := ∀ op ∈ t.thenOps ++ t.elseOps, TxnOp.kmFree op

theorem kmFree_leaseFree (t : TxnModel) (h : TxnModel.kmFree t) : TxnModel.leaseFree t := by
  intro op hop
  have := h op hop
  cases op <;> simp_all [TxnOp.kmFree, TxnOp.leaseFree]

theorem pathsIgnOk_wire (s : List EtcdKv) :
    ∀ ops : List TxnOp, (∀ op ∈ ops, TxnOp.plain op ∧ TxnOp.kmFree op) →
      txn.PathsIgnOk s (ops.map opWire)
  | [], _ => by simp [txn.PathsIgnOk]
  | op :: ops, h => by
    simp only [List.map_cons, txn.PathsIgnOk]
    refine ⟨?_, pathsIgnOk_wire s ops (fun o ho => h o (List.mem_cons_of_mem _ ho))⟩
    obtain ⟨hp, hf⟩ := h op List.mem_cons_self
    cases op with
    | get o => simp [opWire, txn.PathIgnOk]
    | delete o => simp [opWire, txn.PathIgnOk]
    | put k v l => simp [opWire, txn.PathIgnOk]
    | putKeep k v => exact hf.elim
    | putIgnVal k l => exact hf.elim
    | txn _ _ _ => exact hp.elim

/-- **A covered writing transaction's step is the commit of its run.** -/
theorem kvOpStep_txn_km (σ : KVState) (t : TxnModel) (hp : TxnModel.plain t) (hf : TxnModel.kmFree t) :
    kvOpStep (.txn (txnWireOf t)) σ =
      σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnWireOf t)).2.1 := by
  simp only [kvOpStep]
  rw [if_pos]
  rw [txnWireOf_branch]
  exact pathsIgnOk_wire _ _ (fun op ho =>
    ⟨plain_branch t hp _ op ho, hf op (branch_mem t _ op ho)⟩)

/-- A read-only transaction changes nothing. -/
theorem srvRunTxn_ro_nil (r : w64) (s : List EtcdKv) (t : TxnModel) (hp : TxnModel.plain t)
    (hro : (t.thenOps ++ t.elseOps).all TxnOp.isGet = true) : (txn.srvRunTxn r s t).2.1 = [] := by
  have hfl := srvRunTxn_runTxn_flat r s t (flat_branch t hp _)
  have hnil := srvOps_changes_nil s r s _ (plain_branch t hp (txn.txnOk s t))
  apply hnil.2
  show txnWrote (txn.srvRunTxn r s t).2.2 = false
  rw [hfl.2.2]
  unfold runTxn
  exact runOps_gets_noWrite _ _ _ (fun op ho => List.all_eq_true.1 hro op (branch_mem t _ op ho))

theorem prefix_longer {α : Type _} {a b : List α} (h : a <+: b ∨ b <+: a) :
    ∃ c, a <+: c ∧ b <+: c ∧ (c = a ∨ c = b) := by
  rcases h with h | h
  · exact ⟨b, h, List.prefix_refl _, Or.inr rfl⟩
  · exact ⟨a, List.prefix_refl _, h, Or.inl rfl⟩

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **The spec's run is the old proof's**: at the log's length, on its last state, of the model's
transaction. -/
theorem srvRunTxn_km (σ : KVState) (t : TxnModel) (hp : TxnModel.plain t) (hok : kvLogOk σ) :
    txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnWireOf t) =
      txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t := by
  rw [kvLogOk_kvs σ hok, ← (kvLogOk_log hok).2.2.2, srvRunTxn_wire _ _ _ hp]

/-! ## The reply at the adapter's model -/

/-- **A transaction that changed nothing**: its revision the state's, the state the one it read. -/
theorem km_result_nowrite (γ : KMNames) [KMWritable γ] (lo : w64) (pfx : GoString) (t : TxnModel) (resp : Loc)
    (m : TxnRespM) (σ : KVState) (hp : TxnModel.plain t) (hu : t.Under pfx)
    (hg : ∀ o : OpFull, TxnOp.get o ∈ t.thenOps ++ t.elseOps → o.getExact)
    (hok : kvLogOk σ) (h1 : 1 ≤ σ.rev) (h63 : σ.rev + 3 < 2 ^ 63)
    (hlin : t.linearizable = true → sint.Z lo ≤ (σ.rev : Int))
    (hcs : (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.1 = [])
    (hsucc : m.succeeded = (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).1)
    (hrel : opRespsRel false ((txnWireOf t).branch m.succeeded)
      (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.2 m.resps)
    (hrev : m.hdr.revision = W64 (σ.rev : Int)) :
    txnRespMsg (GF := GF) resp m ∗ monoListLbOwn γ.ch σ.changes ⊢
      txnCommitResultTok (EM := etcdModelOfKV γ) pfx lo t resp GoInterface.nil := by
  iintro ⟨#Hm, #Hlb⟩
  have hlen := (kvLogOk_log hok).2.2.2
  have hrc := kvLogOk_rev σ hok
  have hfl := srvRunTxn_runTxn_flat (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t
    (flat_branch t hp _)
  have hnil := srvOps_changes_nil (mvcc.stateAfter σ.log) (W64 (σ.log.length : Int))
    (mvcc.stateAfter σ.log) _ (plain_branch t hp (txn.txnOk (mvcc.stateAfter σ.log) t))
  have hwr : txnWrote (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.2 =
      false := hnil.1 hcs
  have hnr := srvOps_notWrote_noRev (mvcc.stateAfter σ.log) (W64 (σ.log.length : Int))
    (mvcc.stateAfter σ.log) _ (plain_branch t hp (txn.txnOk (mvcc.stateAfter σ.log) t)) hwr
  have hrr : runTxn (W64 (σ.rev : Int)) (mvcc.stateAfter σ.log) t =
      runTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t := by
    unfold runTxn
    simp only
    rw [runOps_noRev _ (W64 (σ.log.length : Int)) _ _ hnr]
  have hU := runTxn_underPfx pfx (W64 (σ.rev : Int)) (mvcc.stateAfter σ.log) t
    (mvcc.stateAfter_sorted σ.log) hp hu
  have hok' : m.succeeded = (runTxn (W64 (σ.rev : Int)) (mvcc.stateAfter σ.log) t).1 := by
    rw [hrr, hsucc, hfl.1]
  have hrs : (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.2 =
      (runTxn (W64 (σ.rev : Int)) (mvcc.stateAfter σ.log) t).2.2 := by
    rw [hrr, hfl.2.2]
  rw [hrs, txnWireOf_branch, hok'] at hrel
  rw [hrs] at hwr
  have hr : sint.Z (W64 (σ.rev : Int)) = (σ.rev : Int) := by word
  ihave ⟨#Hst, %Hwf⟩ := km_etcdState_last γ σ pfx hok $$ Hlb
  ihave ⟨#Hreach, -⟩ := km_reached_of γ σ.changes σ.rev (by omega) (by omega) $$ Hlb
  unfold txnCommitResultTok
  iright
  isplitl []
  · ipureintro; rfl
  iexists (W64 (σ.rev : Int)), (txn.underPfx pfx (mvcc.stateAfter σ.log))
  rw [hU]
  simp only [hwr, Bool.false_eq_true, ↓reduceIte]
  isplitl []
  · iapply txnRespAt_of_msg false resp m _ _ _ _ hrev hok'
      (fun op ho => ⟨plain_branch t hp _ op ho, fun o he => by
        subst he; exact ⟨rfl, hg o (branch_mem t _ _ ho)⟩⟩) hrel $$ Hm
  isplitl []
  · iexact Hreach
  isplitl []
  · ipureintro
    exact ⟨fun h => by rw [hr]; exact hlin h, by rw [hr]; omega, by rw [hr]; omega, Hwf⟩
  isplitl []
  · unfold txnStates
    simp only [hwr, Bool.false_eq_true, ↓reduceIte]
    rw [etcdModelOfKV_etcdState]
    iexact Hst
  itrivial

/-- **A transaction that wrote**: its revision the next, the state it read etcd's at the one
before, the state after it (`σ'`, the commit of its changes: `kvLogOk`, the spec's) etcd's at its
revision, and the revision's token. -/
theorem km_result_wrote (γ : KMNames) [KMWritable γ] (lo : w64) (pfx : GoString) (t : TxnModel) (resp : Loc)
    (m : TxnRespM) (σ σ' : KVState) (hp : TxnModel.plain t) (hu : t.Under pfx)
    (hng : ∀ o : OpFull, TxnOp.get o ∉ t.thenOps ++ t.elseOps)
    (hok : kvLogOk σ) (h63 : σ.rev + 3 < 2 ^ 63) (hlo : sint.Z lo ≤ (σ.rev : Int))
    (hcs : (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.1 ≠ [])
    (heq : σ' = σ.commit (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.1)
    (hok2 : kvLogOk σ')
    (hsucc : m.succeeded = (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).1)
    (hrel : opRespsRel false ((txnWireOf t).branch m.succeeded)
      (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.2 m.resps)
    (hrev : m.hdr.revision = W64 (σ.log.length : Int)) :
    txnRespMsg (GF := GF) resp m ∗ monoListLbOwn γ.ch σ.changes ∗ monoListLbOwn γ.ch σ'.changes ∗
        (if σ'.rev = σ.rev + 1 then
          ghostMapElem (K := Nat) (V := Unit) γ.tok (σ.rev + 1) (DFrac.own 1) ()
         else iprop(True)) ⊢
      txnCommitResultTok (EM := etcdModelOfKV γ) pfx lo t resp GoInterface.nil := by
  subst heq
  have hlen := (kvLogOk_log hok).2.2.2
  have hrc := kvLogOk_rev σ hok
  rw [KVState.commit_rev σ _ hcs, if_pos rfl]
  iintro ⟨#Hm, #Hlb, #Hlb2, Htok⟩
  have hfl := srvRunTxn_runTxn_flat (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t
    (flat_branch t hp _)
  have hnil := srvOps_changes_nil (mvcc.stateAfter σ.log) (W64 (σ.log.length : Int))
    (mvcc.stateAfter σ.log) _ (plain_branch t hp (txn.txnOk (mvcc.stateAfter σ.log) t))
  have hwr : txnWrote (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.2 =
      true := by
    cases h : txnWrote (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.2
    · exact absurd (hnil.2 h) hcs
    · rfl
  have hU := runTxn_underPfx pfx (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t
    (mvcc.stateAfter_sorted σ.log) hp hu
  have hok' : m.succeeded = (runTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).1 := by
    rw [hsucc, hfl.1]
  rw [hfl.2.2, txnWireOf_branch, hok'] at hrel
  rw [hfl.2.2] at hwr
  have hr : sint.Z (W64 (σ.log.length : Int)) = σ.log.length := by word
  have hr1 : W64 (σ.log.length : Int) - W64 1 = W64 (σ.rev : Int) := by
    rw [hlen]; push_cast; word
  -- the states before and after
  ihave ⟨#Hs1, %Hwf1⟩ := km_etcdState_last γ σ pfx hok $$ Hlb
  have hlog2 : (σ.commit (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.1).log =
      σ.log ++ [(txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.1] := by
    simp only [KVState.commit, if_neg hcs]; rfl
  have e2 : mvcc.stateAfter
      (σ.commit (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.1).log =
      (runTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.1 := by
    rw [hlog2, mvcc.stateAfter_append, ← hfl.2.1]
  have er : W64 (((σ.commit (txn.srvRunTxn (W64 (σ.log.length : Int))
      (mvcc.stateAfter σ.log) t).2.1).rev : Nat) : Int) = W64 (σ.log.length : Int) := by
    rw [KVState.commit_rev σ _ hcs, hlen]
  have Hs2e := km_etcdState_last (GF := GF) γ _ pfx hok2
  rw [e2, er] at Hs2e
  ihave ⟨#Hs2, -⟩ := Hs2e $$ Hlb2
  have hc2 : (σ.commit (txn.srvRunTxn (W64 (σ.log.length : Int))
      (mvcc.stateAfter σ.log) t).2.1).changes.length = σ.log.length := by
    simp only [KVState.commit, if_neg hcs, List.length_append, List.length_singleton]; omega
  ihave ⟨#Hreach, -⟩ := km_reached_of γ _ σ.log.length (by omega) (by omega) $$ Hlb2
  unfold txnCommitResultTok
  iright
  isplitl []
  · ipureintro; rfl
  iexists (W64 (σ.log.length : Int)), (txn.underPfx pfx (mvcc.stateAfter σ.log))
  rw [hU]
  simp only [hwr, ↓reduceIte]
  isplitl []
  · iapply txnRespAt_of_msg false resp m _ _ _ _ hrev hok'
      (fun op ho => ⟨plain_branch t hp _ op ho, fun o he => by
        subst he; exact absurd (branch_mem t _ _ ho) (hng o)⟩) hrel $$ Hm
  isplitl []
  · iexact Hreach
  isplitl []
  · ipureintro
    exact ⟨fun _ => by rw [hr]; omega, by rw [hr]; omega, by rw [hr]; omega, Hwf1⟩
  isplitl []
  · unfold txnStates
    simp only [↓reduceIte]
    rw [hr1, etcdModelOfKV_etcdState]
    isplitl
    · iexact Hs1
    · iexact Hs2
  rw [etcdModelOfKV_etcdRevToken]
  unfold kmRevTok
  rw [show (sint.Z (W64 (σ.log.length : Int))).toNat = σ.rev + 1 by rw [hr]; omega]
  iexact Htok

/-! ## The commit -/

/-- **A transaction the spec's updates cover**: read-only and linearizable (a read update), or
writing and `kmFree` (a write's update, `checkTxn` passing). -/
def kmCovered (t : TxnModel) : Prop :=
  (txn.txnReadonly (txnWireOf t) = true ∧ t.linearizable = true) ∨
    (txn.txnReadonly (txnWireOf t) = false ∧ TxnModel.kmFree t)

/-- **`Commit()` on a builder of a client of etcd's KV, at the adapter's model** (a covered
transaction, `kmCovered`): `txnCommitResultTok` from `etcdReached lo`, its error a client error. -/
theorem kv_txn_commit_km (api tp : Loc) (addr : List GoString) (γ : KMNames) [KMWritable γ] (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (b : TxnBuild) (lo : w64) (pfx : GoString)
    (hp : TxnModel.plain b.model) (hu : b.model.Under pfx) (hx : b.model.exactGets)
    (hk : kmCovered b.model) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
        txnKvIs tp api ∗ isKv api γ.kv false ∗ kmInv γ ∗ kmReachedAt γ (W64 1) ∗
        etcdReached (EM := etcdModelOfKV γ) lo }}
      (App (Val #(methods (txnIfaceOf tp).ty go!"Commit" (txnIfaceOf tp).v)) (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        txnCommitResultTok (EM := etcdModelOfKV γ) pfx lo b.model resp err ∗
        (⌜err = GoInterface.nil⌝ ∨ ⌜err ≠ GoInterface.nil ∧ clientErr err⌝) }} := by
  iintro %Φ ⟨#Pc, Hobj, #Hkp, #Hkv, #Hinv, #H1, #Hlo⟩ HΦ
  -- the floor: changes the client saw, `lo` of them or more, and at least one
  imod km_reached_lb γ lo $$ Hlo with ⟨%l0, #Hl0, %Hll⟩
  iunfold kmReachedAt at H1
  icases H1 with ⟨%l1, #Hl1, %Hl1⟩
  ihave %Hc := mono_list_lb_valid γ.ch l0 l1 $$ Hl0 Hl1
  obtain ⟨lf, p0, p1, hlf⟩ := prefix_longer Hc
  ihave #Hlf : monoListLbOwn γ.ch lf $$ []
  · rcases hlf with rfl | rfl
    · iexact Hl0
    · iexact Hl1
  have hz1 : sint.Z (W64 1) = 1 := by word
  have hl0 := p0.length_le
  have hl1 := p1.length_le
  have hser := txnSerializable_wire b.model
  rcases hk with ⟨hro, hlin⟩ | ⟨hro, hfree⟩
  · -- read-only, linearizable: the read update after the floor
    have hs : txn.txnSerializable (txnWireOf b.model) = false := by rw [hser, hlin]; rfl
    ihave #Hau := km_read_au γ lf $$ [$Hinv $Hlf]
    iapply (v3.txn.wp_Commit tp addr api γ.kv false ci cd b (kmSeenQ γ lf)) $$ [Hobj]
    · iframe
      iframe #
      isplitl []
      · ipureintro; exact ⟨hp, txnModelIn_wire _ hx⟩
      simp only [intuitionisticallyIf, Bool.false_eq_true, ↓reduceIte]
      iright; ileft
      isplitl []
      · ipureintro; exact ⟨hro, hs⟩
      iunfold kvReadAu at Hau
      iunfold kvAu at Hau
      iexact Hau
    simp only [hro, hs, ↓reduceIte, Bool.false_eq_true]
    inext
    iintro %resp %err Hout
    iapply HΦ
    icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hs⟩ | ⟨%Herr, #Hke⟩)
    · subst Herr
      iunfold kmSeenQ at HQ
      icases HQ with ⟨#Hlb, %Hpre⟩
      obtain ⟨hsucc, hrel, hrev, h63, hok, -⟩ := Hs
      rw [srvRunTxn_km σ _ hp hok] at hsucc hrel
      have hrc := kvLogOk_rev σ hok
      have hlp := Hpre.length_le
      have hall := hro
      rw [txnReadonly_wire] at hall
      isplitl
      · iapply (km_result_nowrite γ lo pfx b.model resp m σ hp hu
          (fun o ho => (hx.1 o ho).2) hok (by omega) h63 (fun _ => by omega)
          (srvRunTxn_ro_nil _ _ _ hp hall) hsucc hrel hrev) $$ [$Hm $Hlb]
      · ileft; ipureintro; rfl
    · iunfold kvErr at Hke
      icases Hke with ⟨%Hce, -, -⟩
      isplitl []
      · unfold txnCommitResultTok; ileft; ipureintro; exact Herr.1
      · iright; ipureintro; exact ⟨Herr.1, Hce⟩
  · -- writing, covered: the write's update after the floor
    have hl := kmFree_leaseFree _ hfree
    ihave Hau := km_write_au γ lf (.txn (txnWireOf b.model)) (KMWritable.keep _) $$ [$Hinv $Hlf]
    iapply (v3.txn.wp_Commit tp addr api γ.kv false ci cd b
      (kmWriteQ γ lf (.txn (txnWireOf b.model)))) $$ [Hobj Hau]
    · iframe
      iframe #
      isplitl []
      · ipureintro; exact ⟨hp, txnModelIn_wire _ hx⟩
      simp only [intuitionisticallyIf, Bool.false_eq_true, ↓reduceIte]
      iright; iright
      isplitl []
      · ipureintro; exact ⟨hro, txnPlain_wire _ hp hx hl, txnNoZeroEnd_wire _ hp hx hro⟩
      iunfold kvOpAu1 at Hau
      iunfold kvAu1 at Hau
      iexact Hau
    simp only [hro, ↓reduceIte, Bool.false_eq_true]
    inext
    iintro %resp %err Hout
    iapply HΦ
    icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hs⟩ | ⟨%Herr, #Hke⟩)
    · subst Herr
      iunfold kmWriteQ at HQ
      icases HQ with ⟨#Hlb2, #Hlb, %Hpre, Htok⟩
      obtain ⟨hsucc, hrel, hrev, h63, hok, hok2⟩ := Hs
      have hok2 := hok2 trivial
      have hstep := kvOpStep_txn_km σ _ hp hfree
      rw [srvRunTxn_km σ _ hp hok] at hsucc hrel hrev hstep hok2
      have hrc := kvLogOk_rev σ hok
      have hlen := (kvLogOk_log hok).2.2.2
      have hlp := Hpre.length_le
      obtain ⟨hng, -, -⟩ := hx.2 (by rw [← txnReadonly_wire]; exact hro)
      isplitl
      · by_cases hcs : (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log)
            b.model).2.1 = []
        · rw [hcs, KVState.commit_nil] at hrev
          iclear Htok Hlb2
          iapply (km_result_nowrite γ lo pfx b.model resp m σ hp hu
            (fun o ho => absurd ho (hng o)) hok (by omega) h63 (fun _ => by omega)
            hcs hsucc hrel hrev) $$ [$Hm $Hlb]
        · rw [KVState.commit_rev σ _ hcs, ← hlen] at hrev
          rw [← hstep] at hok2
          iapply (km_result_wrote γ lo pfx b.model resp m σ _ hp hu hng hok h63 (by omega)
            hcs hstep hok2 hsucc hrel hrev) $$ [$Hm $Hlb $Hlb2 $Htok]
      · ileft; ipureintro; rfl
    · iunfold kvErr at Hke
      icases Hke with ⟨%Hce, -, -⟩
      isplitl []
      · unfold txnCommitResultTok; ileft; ipureintro; exact Herr.1
      · iright; ipureintro; exact ⟨Herr.1, Hce⟩

/-- **`Commit()` on a builder of a client of etcd's KV, any result** (`txnAnyResult`): a
read-only transaction with no update, a covered writing one with a write's update. -/
theorem kv_txn_commit_any_km (api tp : Loc) (addr : List GoString) (γ : KMNames) [KMWritable γ]
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild)
    (hp : TxnModel.plain b.model) (hx : b.model.exactGets)
    (hk : txn.txnReadonly (txnWireOf b.model) = true ∨ TxnModel.kmFree b.model) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
        txnKvIs tp api ∗ isKv api γ.kv false ∗ kmInv γ }}
      (App (Val #(methods (txnIfaceOf tp).ty go!"Commit" (txnIfaceOf tp).v)) (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); txnAnyResult resp err }} := by
  iintro %Φ ⟨#Pc, Hobj, #Hkp, #Hkv, #Hinv⟩ HΦ
  imod (monoListLbOwn_nil (GF := GF) (A := List mvcc.Change) γ.ch) with #H0
  ihave Hupd : iprop(∃ Q : KVState → IProp GF,
      ⌜txn.txnReadonly (txnWireOf b.model) = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly (txnWireOf b.model) = true ∧
          txn.txnSerializable (txnWireOf b.model) = false⌝ ∗
          □ AU <{ ∃∃ (σ : KVState), etcdKV γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
            <{ etcdKV γ.kv σ, COMM □ Q σ }>) ∨
        (⌜txn.txnReadonly (txnWireOf b.model) = false ∧ txn.txnPlain (txnWireOf b.model) ∧
          txnNoZeroEnd (txnWireOf b.model)⌝ ∗
          AU <{ ∃∃ (σ : KVState), etcdKV γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
            <{ etcdKV γ.kv (kvOpStep (.txn (txnWireOf b.model)) σ), COMM Q σ }>)) $$ []
  · cases hro : txn.txnReadonly (txnWireOf b.model)
    · have hf : TxnModel.kmFree b.model := by
        rcases hk with h | h
        · rw [hro] at h; cases h
        · exact h
      ihave Hau := km_write_au γ [] (.txn (txnWireOf b.model)) (KMWritable.keep _) $$ [$Hinv $H0]
      iexists (kmWriteQ γ [] (.txn (txnWireOf b.model)))
      iright; iright
      isplitl []
      · ipureintro
        exact ⟨rfl, txnPlain_wire _ hp hx (kmFree_leaseFree _ hf), txnNoZeroEnd_wire _ hp hx hro⟩
      iunfold kvOpAu1 at Hau
      iunfold kvAu1 at Hau
      iexact Hau
    · iexists (fun _ => iprop(True))
      ileft; ipureintro; exact ⟨rfl, rfl⟩
  icases Hupd with ⟨%Q, Hu⟩
  iapply (v3.txn.wp_Commit tp addr api γ.kv false ci cd b Q) $$ [Hobj Hu]
  · simp only [intuitionisticallyIf, Bool.false_eq_true, ↓reduceIte]
    iframe
    iframe #
    ipureintro; exact ⟨hp, txnModelIn_wire _ hx⟩
  inext
  iintro %resp %err Hout
  iapply HΦ
  unfold txnAnyResult
  icases Hout with (⟨%Herr, %m, %σ, #Hm, -⟩ | ⟨%Herr, -⟩)
  · iright
    isplitl []
    · ipureintro; exact Herr
    iunfold txnRespMsg at Hm
    icases Hm with ⟨%Hrn, %h, %sl, %ps, #Hh, -, #Hok, -⟩
    iexists h, m.succeeded
    iframe Hh Hok
  · ileft; ipureintro; exact Herr.1

/-! ## The bridge -/

/-- **The transactions the spec's updates do not cover, their `Commit()`** (a premise,
persistent; see the file header): for a builder of `api` whose `exactGets` transaction is not
`kmCovered` (read-only and serializable, or writing with a lease or an `IgnoreValue` put),
`txnCommitResultTok` from `etcdReached lo` under a prefix, with a client error; and, for a writing
one, `txnAnyResult`. -/
def kmTxnUncoveredTodo (api : Loc) (γ : KMNames) [KMWritable γ] : IProp GF :=
  iprop(□ ∀ (tp : Loc) (addr : List GoString) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (b : TxnBuild),
    ⌜TxnModel.plain b.model ∧ b.model.exactGets ∧ ¬ kmCovered b.model⌝ -∗ txnKvIs tp api -∗
    ((□ ∀ (lo : w64) (pfx : GoString), ⌜b.model.Under pfx⌝ -∗
      {{ txnObjAt tp addr ci cd b ∗ etcdReached (EM := etcdModelOfKV γ) lo }}
        (App (Val #(methods (txnIfaceOf tp).ty go!"Commit" (txnIfaceOf tp).v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          txnCommitResultTok (EM := etcdModelOfKV γ) pfx lo b.model resp err ∗
          (⌜err = GoInterface.nil⌝ ∨ ⌜err ≠ GoInterface.nil ∧ clientErr err⌝) }}) ∗
     (⌜txn.txnReadonly (txnWireOf b.model) = false⌝ -∗
      {{ txnObjAt tp addr ci cd b }}
        (App (Val #(methods (txnIfaceOf tp).ty go!"Commit" (txnIfaceOf tp).v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); txnAnyResult resp err }})))

instance kmTxnUncoveredTodo_persistent (api : Loc) (γ : KMNames) [KMWritable γ] :
    Persistent (kmTxnUncoveredTodo (GF := GF) api γ) := by
  unfold kmTxnUncoveredTodo; infer_instance

theorem isKv_kvObjAt (api : Loc) (γ : KVNames) (dup : Bool) :
    isKv (GF := GF) api γ dup ⊢ ∃ addr : List GoString, kvObjAt api addr := by
  unfold isKv isKvOf
  iintro ⟨%ms, #Ho, -⟩
  iexists _
  iexact Ho

/-- **A client of etcd's KV meets the recipes' transaction contract** (`isEtcdTxnKVTodo`) at the
adapter's model (see the file header). Premises: that `errors.As` can take
`*rpctypes.EtcdError` (`hAs`), that the client's errors are client errors as `errors.Is` sees
them (`clientErrsIs`), a state of revision `1` seen (`kmReachedAt γ (W64 1)`), and the uncovered
transactions' commits (`kmTxnUncoveredTodo`). -/
theorem isEtcdTxnKVTodo_of_km (api : Loc) (γ : KMNames) [KMWritable γ] (pfx : GoString)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv api γ.kv false ∗
        kmInv γ ∗ kmReachedAt γ (W64 1) ∗ clientErrsIs ∗ kmTxnUncoveredTodo api γ ⊢
      isEtcdTxnKVTodo (EM := etcdModelOfKV γ) (kvIfaceOf api) pfx := by
  iintro ⟨#Pc, #Hkv, #Hinv, #H1, #Hcei, #Hun⟩
  ihave ⟨%addr, #Hko⟩ := isKv_kvObjAt api γ.kv false $$ Hkv
  unfold isEtcdTxnKVTodo
  iintro !> %Φ !> - HΦ
  imod (todo_ctx (GF := GF) hAs) with ⟨%cd, #Hctx, #Hce⟩
  iapply (v3.kv.wp_Txn api addr todoCtxVal cd) $$ []
  · iframe #
  inext
  iintro %t ⟨%tp, %Ht, Hobj, #Htk⟩
  subst Ht
  iapply HΦ $$ %(txnIfaceOf tp)
  iexists (txnB tp addr cd)
  -- the commit at a floor, for both commit triples
  have hcommit : ∀ (b : TxnBuild) (lo : w64), b.model.Under pfx → b.model.exactGets →
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnKvIs tp api ∗
        isKv api γ.kv false ∗ kmInv γ ∗ kmReachedAt γ (W64 1) ∗ kmTxnUncoveredTodo api γ ⊢
      {{ txnB tp addr cd b ∗ etcdReached (EM := etcdModelOfKV γ) lo }}
        (App (Val #(methods (txnIfaceOf tp).ty go!"Commit" (txnIfaceOf tp).v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          txnCommitResultTok (EM := etcdModelOfKV γ) pfx lo b.model resp err ∗
          (⌜err = GoInterface.nil⌝ ∨ ⌜err ≠ GoInterface.nil ∧ clientErr err⌝) }} := by
    intro b lo hu hx
    iintro ⟨#Pc, #Htk, #Hkv, #Hinv, #H1, #Hun⟩ !> %Φ ⟨HB, #Hlo⟩ HΦ
    iunfold txnB at HB
    icases HB with ⟨Hobj, %hp⟩
    by_cases hk : kmCovered b.model
    · iapply (kv_txn_commit_km api tp addr γ todoCtxVal cd b lo pfx hp hu hx hk) $$ [Hobj] HΦ
      iframe
      iframe #
    · iunfold kmTxnUncoveredTodo at Hun
      ihave ⟨#Ht, -⟩ := Hun $$ %tp %addr %todoCtxVal %cd %b %(⟨hp, hx, hk⟩) Htk
      ihave #Ht' := Ht $$ %lo %pfx %hu
      iapply Ht' $$ [Hobj] HΦ
      iframe Hobj Hlo
  isplitl [Hobj]
  · unfold txnB
    iframe
    ipureintro
    exact ⟨fun _ h => by simp [TxnBuild.empty, TxnModel.empty] at h,
      fun _ h => by simp [TxnBuild.empty, TxnModel.empty] at h⟩
  isplitl []
  · unfold txnBuilderSpecX
    isplitl []
    · iintro !> %b %sl %ms %Φ' !> ⟨HB, Hc, %hf⟩ HΦ'
      iunfold txnB at HB
      icases HB with ⟨Hobj, %hp⟩
      iapply (v3.txn.wp_If tp addr todoCtxVal cd b sl ms) $$ [Hobj Hc]
      · iframe; iframe #; ipureintro; exact hf
      inext
      iintro Hobj
      iapply HΦ'
      unfold txnB
      iframe
      ipureintro; exact hp
    isplitl []
    · iintro !> %b %sl %os %ops %Φ' !> ⟨HB, Hos, %hf⟩ HΦ'
      iunfold txnB at HB
      icases HB with ⟨Hobj, %hp⟩
      iapply (v3.txn.wp_Then tp addr todoCtxVal cd b sl os ops) $$ [Hobj Hos]
      · iframe; iframe #; ipureintro; exact hf
      inext
      iintro Hobj
      iapply HΦ'
      unfold txnB
      iframe
      ipureintro
      have h2 := plain_append_ops os ops hf.1
      exact ⟨fun op h => by
        rcases List.mem_append.1 h with h | h
        · exact hp.1 op h
        · exact h2 op h, hp.2⟩
    isplitl []
    · iintro !> %b %sl %os %ops %Φ' !> ⟨HB, Hos, %hf⟩ HΦ'
      iunfold txnB at HB
      icases HB with ⟨Hobj, %hp⟩
      iapply (v3.txn.wp_Else tp addr todoCtxVal cd b sl os ops) $$ [Hobj Hos]
      · iframe; iframe #; ipureintro; exact hf
      inext
      iintro Hobj
      iapply HΦ'
      unfold txnB
      iframe
      ipureintro
      have h2 := plain_append_ops os ops hf.1
      exact ⟨hp.1, fun op h => by
        rcases List.mem_append.1 h with h | h
        · exact hp.2 op h
        · exact h2 op h⟩
    isplitl []
    · iintro !> %b %lo %Φ' !> ⟨HB, #Hlo, %hux⟩ HΦ'
      iapply (hcommit b lo hux.1 hux.2) $$ [$Pc $Htk $Hkv $Hinv $H1 $Hun] [HB]
      · iframe; iframe #
      inext
      iintro %resp %err ⟨Hr, -⟩
      iapply HΦ'
      iexact Hr
    · iintro !> %b %Φ' !> ⟨HB, %hx⟩ HΦ'
      iunfold txnB at HB
      icases HB with ⟨Hobj, %hp⟩
      by_cases hk : txn.txnReadonly (txnWireOf b.model) = true ∨ TxnModel.kmFree b.model
      · iapply (kv_txn_commit_any_km api tp addr γ todoCtxVal cd b hp hx hk) $$ [Hobj] HΦ'
        iframe
        iframe #
      · -- a writing transaction with a lease or an `IgnoreValue` put: the premise
        have hk1 : txn.txnReadonly (txnWireOf b.model) = false := by
          cases h : txn.txnReadonly (txnWireOf b.model)
          · rfl
          · exact absurd (Or.inl h) hk
        have hk2 : ¬ kmCovered b.model := by
          rintro (⟨h, -⟩ | ⟨-, h⟩)
          · rw [hk1] at h; cases h
          · exact hk (Or.inr h)
        iunfold kmTxnUncoveredTodo at Hun
        ihave ⟨-, #Ht⟩ := Hun $$ %tp %addr %todoCtxVal %cd %b %(⟨hp, hx, hk2⟩) Htk
        iapply Ht $$ %hk1 [Hobj] HΦ'
        iexact Hobj
  · unfold txnCommitErrTodo
    iintro !> %b %lo %Φ' !> ⟨HB, #Hlo, %hux⟩ HΦ'
    iapply (hcommit b lo hux.1 hux.2) $$ [$Pc $Htk $Hkv $Hinv $H1 $Hun] [HB]
    · iframe; iframe #
    inext
    iintro %resp %err ⟨Hr, Herr⟩
    iapply HΦ'
    iframe Hr
    icases Herr with (%He | %He)
    · ileft; ipureintro; exact He
    · iright
      iunfold clientErrsIs at Hcei
      iapply Hcei $$ %err %He.2

end proofs

end client
end EtcdGrove
end Perennial
