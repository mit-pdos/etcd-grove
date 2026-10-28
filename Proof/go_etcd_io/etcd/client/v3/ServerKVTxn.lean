/-
**A real `*kv`'s transactions meet the recipes' transaction contract at the server's model** (the
vertical slice's unit V2b, 2026-10-14; `InvServerKV.lean`). Lean-first, no Rocq counterpart.

`isEtcdTxnKVTodo_of_kv`: `kv.Txn(context.TODO())` on a `*kv` over a connection to a gRPC server at
`addr` where etcd's `Txn` is registered returns a builder (`txnObjAt`, the `*txn`'s fields: the
abstract state `B` of `txnBuilderSpecX`) whose `If`, `Then`, `Else` are the client's (`txn.If`, ...)
and whose `Commit`, for an `exactGets` transaction under `pfx`, returns `txnCommitResultTok` in the
server's model (`v3rpc.etcdModelOfServer E`), the token iff it wrote, and its error a client error
(`txnCommitErrTodo`, with the premise `clientErrsIs`); for any `exactGets` transaction,
`txnAnyResult`.

* **The wire's transaction is the model's** (`srvRunTxn_wire`): the request `Commit` sends is
  `txnWireOf b.model` (gets and deletes as the wire carries them); the server's run of it is its
  run of the model's (same selections and counts).
* **The server's run is the client's** (`srvRunTxn_runTxn_flat`, the txn package's: no nested
  transaction, the builder's operations are plain), and **restricted to the prefix** it is the
  client model's run on etcd's state under the prefix (`runTxn_underPfx`: comparisons, gets,
  puts and deletes under the prefix commute with the restriction).
* **It wrote iff its changes are not empty** (`srvOps_changes_nil`): so the revision is the log's
  next and the token minted iff it wrote.
* **The response is the model's** (`txnRespAt_of_msg`): the reply's message answers the run
  (`opRespsRel`); for the gets of an `exactGets` transaction, `rangeKvsOk` of the `Op`'s (the
  server answers as the model says, `ServerKVGet.lean`'s `wire_answer` facts).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ServerKVGet
public import Proof.go_etcd_io.etcd.client.v3.ServerKVPut

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The wire's transaction -/

theorem deleteWire_key (o : OpFull) : (deleteWireOf o).key = o.key ∧
    (deleteWireOf o).base.rangeEnd = o.base.rangeEnd := by
  simp [deleteWireOf, txn.deleteOpOf, op_simps]

theorem rangeIn_rangeWire (s : List EtcdKv) (o : OpFull) : rangeIn s (rangeWireOf o) = rangeIn s o := by
  obtain ⟨h1, h2, -⟩ := wire_fields o
  simp only [rangeIn, h1, h2]

theorem rangeIn_deleteWire (s : List EtcdKv) (o : OpFull) : rangeIn s (deleteWireOf o) = rangeIn s o := by
  obtain ⟨h1, h2⟩ := deleteWire_key o
  simp only [rangeIn, h1, h2]

theorem srvOp_opWire (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (op : TxnOp)
    (hp : TxnOp.plain op) : txn.srvOp s0 r s (opWire op) = txn.srvOp s0 r s op := by
  cases op with
  | txn cs ts es => exact hp.elim
  | get o => simp only [opWire, txn.srvOp, wire_rangeSel, rangeIn_rangeWire]
  | delete o => simp only [opWire, txn.srvOp, rangeIn_deleteWire]
  | put k v l => simp [opWire]
  | putKeep k v => simp [opWire]
  | putIgnVal k l => simp [opWire]

theorem srvOps_map_opWire (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), (∀ op ∈ ops, TxnOp.plain op) →
      txn.srvOps s0 r s (ops.map opWire) = txn.srvOps s0 r s ops
  | s, [], _ => rfl
  | s, op :: ops, hp => by
    simp only [List.map_cons, txn.srvOps_cons]
    rw [srvOp_opWire s0 r s op (hp op List.mem_cons_self),
      srvOps_map_opWire s0 r _ ops (fun o ho => hp o (List.mem_cons_of_mem _ ho))]

theorem txnWireOf_branch (t : TxnModel) (ok : Bool) :
    (txnWireOf t).branch ok = (t.branch ok).map opWire := by
  cases ok <;> rfl

/-- **The server's run of the wire's transaction is its run of the model's**. -/
theorem srvRunTxn_wire (r : w64) (s : List EtcdKv) (t : TxnModel) (hp : TxnModel.plain t) :
    txn.srvRunTxn r s (txnWireOf t) = txn.srvRunTxn r s t := by
  have hb : ∀ ok, ∀ op ∈ t.branch ok, TxnOp.plain op := by
    intro ok op hop
    cases ok
    · exact hp.2 op hop
    · exact hp.1 op hop
  unfold txn.srvRunTxn txn.txnOk
  rw [show (txnWireOf t).cmps = t.cmps from rfl, txnWireOf_branch,
    srvOps_map_opWire _ _ _ _ (hb _)]

/-! ## Restricted to the prefix -/

theorem cmpHolds_underPfx (pfx : GoString) (s : List EtcdKv) (c : CmpModel)
    (h : KeyRangeUnder pfx c.key c.rangeEnd) : cmpHolds (txn.underPfx pfx s) c = cmpHolds s c := by
  have hf : (txn.underPfx pfx s).filter (fun v => inRange c.key c.rangeEnd v.key) =
      s.filter (fun v => inRange c.key c.rangeEnd v.key) := by
    unfold txn.underPfx
    rw [List.filter_filter]
    apply List.filter_congr
    intro v _
    by_cases hi : inRange c.key c.rangeEnd v.key = true
    · simp [hi, h v.key hi]
    · simp [hi]
  unfold cmpHolds
  simp only [hf]

theorem applyTxnOp_sorted (r : w64) (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (op : TxnOp)
    (hp : TxnOp.plain op) : (applyTxnOp r s op).1.Pairwise etcdKvLess := by
  cases op with
  | txn cs ts es => exact hp.elim
  | get o => exact hs
  | delete o => exact hs.filter _
  | put k v l => simp only [applyTxnOp]; unfold putKv; exact btInsert_sorted etcdKvLess_swo hs
  | putKeep k v => simp only [applyTxnOp]; unfold putKv; exact btInsert_sorted etcdKvLess_swo hs
  | putIgnVal k l => simp only [applyTxnOp]; unfold putKv; exact btInsert_sorted etcdKvLess_swo hs

theorem applyTxnOp_underPfx (pfx : GoString) (r : w64) (s : List EtcdKv)
    (hs : s.Pairwise etcdKvLess) (op : TxnOp) (hp : TxnOp.plain op) (hu : op.Under pfx) :
    applyTxnOp r (txn.underPfx pfx s) op =
      (txn.underPfx pfx (applyTxnOp r s op).1, (applyTxnOp r s op).2) := by
  cases op with
  | txn cs ts es => exact hp.elim
  | get o =>
    simp only [TxnOp.Under] at hu
    simp only [applyTxnOp, v3rpc.rangeSel_underPfx pfx s o hu, v3rpc.rangeIn_underPfx pfx s o hu]
  | delete o =>
    simp only [TxnOp.Under] at hu
    exact applyTxnOp_delete_underPfx pfx r s o hu
  | put k v l =>
    exact applyTxnOp_put_underPfx pfx r s hs _ rfl (fun _ h => TxnOp.noConfusion h)
      (fun _ _ _ h => TxnOp.noConfusion h) hu
  | putKeep k v =>
    exact applyTxnOp_put_underPfx pfx r s hs _ rfl (fun _ h => TxnOp.noConfusion h)
      (fun _ _ _ h => TxnOp.noConfusion h) hu
  | putIgnVal k l =>
    exact applyTxnOp_put_underPfx pfx r s hs _ rfl (fun _ h => TxnOp.noConfusion h)
      (fun _ _ _ h => TxnOp.noConfusion h) hu

theorem runOps_underPfx (pfx : GoString) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), s.Pairwise etcdKvLess →
      (∀ op ∈ ops, TxnOp.plain op ∧ op.Under pfx) →
      runOps r (txn.underPfx pfx s) ops = (txn.underPfx pfx (runOps r s ops).1, (runOps r s ops).2)
  | s, [], _, _ => rfl
  | s, op :: ops, hs, hp => by
    obtain ⟨h1, h2⟩ := hp op List.mem_cons_self
    have ih := runOps_underPfx pfx r (applyTxnOp r s op).1 ops (applyTxnOp_sorted r s hs op h1)
      (fun o ho => hp o (List.mem_cons_of_mem _ ho))
    simp only [runOps]
    rw [applyTxnOp_underPfx pfx r s hs op h1 h2]
    simp only
    rw [ih]

/-- **A transaction under the prefix, on etcd's state restricted to it**: the same verdict and
results, the state after it the restriction of the full state's (plain operations). -/
theorem runTxn_underPfx (pfx : GoString) (r : w64) (s : List EtcdKv) (t : TxnModel)
    (hs : s.Pairwise etcdKvLess) (hp : TxnModel.plain t) (hu : t.Under pfx) :
    runTxn r (txn.underPfx pfx s) t =
      ((runTxn r s t).1, txn.underPfx pfx (runTxn r s t).2.1, (runTxn r s t).2.2) := by
  have hc : t.cmps.all (cmpHolds (txn.underPfx pfx s)) = t.cmps.all (cmpHolds s) := by
    exact all_congr_mem _ _ _ (fun c hc => cmpHolds_underPfx pfx s c (hu.1 c hc))
  have hb : ∀ ok, ∀ op ∈ t.branch ok, TxnOp.plain op ∧ op.Under pfx := by
    intro ok op hop
    cases ok
    · exact ⟨hp.2 op hop, hu.2.2 op hop⟩
    · exact ⟨hp.1 op hop, hu.2.1 op hop⟩
  unfold runTxn
  simp only [hc]
  rw [runOps_underPfx pfx r s _ hs (hb _)]

/-! ## Wrote iff changed -/

theorem srvOps_changes_nil (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), (∀ op ∈ ops, TxnOp.plain op) →
      ((txn.srvOps s0 r s ops).1 = [] ↔ txnWrote (txn.srvOps s0 r s ops).2 = false)
  | s, [], _ => by simp [txn.srvOps, txnWrote]
  | s, op :: ops, hp => by
    have ih := srvOps_changes_nil s0 r (mvcc.applyChanges r s (txn.srvOp s0 r s op).1) ops
      (fun o ho => hp o (List.mem_cons_of_mem _ ho))
    rw [txn.srvOps_cons]
    simp only [List.append_eq_nil_iff, txnWrote, List.any_cons, Bool.or_eq_false_iff] at ih ⊢
    rw [ih]
    have h1 := hp op List.mem_cons_self
    have hop : (txn.srvOp s0 r s op).1 = [] ↔ (txn.srvOp s0 r s op).2.wrote = false := by
      cases op with
      | txn cs ts es => exact h1.elim
      | get o => simp [txn.srvOp, TxnOpResult.wrote]
      | delete o => simp [txn.srvOp, TxnOpResult.wrote]
      | put k v l => simp [txn.srvOp, TxnOpResult.wrote]
      | putKeep k v => simp [txn.srvOp, TxnOpResult.wrote]
      | putIgnVal k l => simp [txn.srvOp, TxnOpResult.wrote]
    rw [hop]

/-! ## Gets and deletes only: the revision does not matter -/

/-- A get or a delete (no revision of its own in the model's run). -/
def TxnOp.noRev : TxnOp → Prop
  | .get _ => True
  | .delete _ => True
  | _ => False

theorem runOps_noRev (r r' : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), (∀ op ∈ ops, TxnOp.noRev op) →
      runOps r s ops = runOps r' s ops
  | s, [], _ => rfl
  | s, op :: ops, h => by
    have h0 := h op List.mem_cons_self
    have ih := fun s' => runOps_noRev r r' s' ops (fun o ho => h o (List.mem_cons_of_mem _ ho))
    have ha : applyTxnOp r s op = applyTxnOp r' s op := by
      cases op with
      | get o => rfl
      | delete o => rfl
      | _ => exact h0.elim
    simp only [runOps]
    rw [ha, ih]

/-- A branch that did not write has no put (a put's result is a write). -/
theorem srvOps_notWrote_noRev (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), (∀ op ∈ ops, TxnOp.plain op) →
      txnWrote (txn.srvOps s0 r s ops).2 = false → ∀ op ∈ ops, TxnOp.noRev op
  | s, [], _, _ => by simp
  | s, op :: ops, hp, hw => by
    rw [txn.srvOps_cons] at hw
    simp only [txnWrote, List.any_cons, Bool.or_eq_false_iff] at hw
    obtain ⟨h0, h1⟩ := hw
    have ih := srvOps_notWrote_noRev s0 r _ ops (fun o ho => hp o (List.mem_cons_of_mem _ ho)) h1
    intro o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · have := hp o List.mem_cons_self
      cases o with
      | get _ => trivial
      | delete _ => trivial
      | txn _ _ _ => exact this.elim
      | put _ _ _ => simp [txn.srvOp, TxnOpResult.wrote] at h0
      | putKeep _ _ => simp [txn.srvOp, TxnOpResult.wrote] at h0
      | putIgnVal _ _ => simp [txn.srvOp, TxnOpResult.wrote] at h0
    · exact ih o ho

/-! ## The wire's request has no `[0]` range end; the transaction's log -/

theorem opIsGet_opWire (op : TxnOp) : txn.opIsGet (opWire op) = TxnOp.isGet op := by
  cases op <;> simp [opWire, txn.opIsGet, TxnOp.isGet]

theorem txnReadonly_wire (t : TxnModel) :
    txn.txnReadonly (txnWireOf t) = (t.thenOps ++ t.elseOps).all TxnOp.isGet := by
  unfold txn.txnReadonly txnWireOf
  simp only [← List.map_append, List.all_map]
  exact all_congr_mem _ _ _ (fun op _ => opIsGet_opWire op)

/-- The wire's transaction is serializable iff the model's is not linearizable (unit W-M3). -/
theorem opIsSerGet_opWire (op : TxnOp) : txn.opIsSerGet (opWire op) = !TxnOp.linearizable op := by
  cases op <;> simp [txn.opIsSerGet, opWire, TxnOp.linearizable, (wire_fields _).2.2.2.2.2.2.1]

theorem txnSerializable_wire (t : TxnModel) :
    txn.txnSerializable (txnWireOf t) = !t.linearizable := by
  unfold txn.txnSerializable txnWireOf TxnModel.linearizable
  simp only [← List.map_append, List.all_map]
  induction t.thenOps ++ t.elseOps with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.all_cons, List.any_cons, Function.comp, opIsSerGet_opWire, ih, Bool.not_or]

/-- A transaction that writes is linearizable (an operation not a get is). -/
theorem linearizable_of_write (t : TxnModel) (h : txn.txnReadonly (txnWireOf t) = false) :
    t.linearizable = true := by
  rw [txnReadonly_wire, List.all_eq_false] at h
  unfold TxnModel.linearizable
  obtain ⟨op, hop, hng⟩ := h
  exact List.any_eq_true.2 ⟨op, hop, by cases op <;> simp_all [TxnOp.isGet, TxnOp.linearizable]⟩

theorem txnNoZeroEnd_wire0 (t : TxnModel) (hp : TxnModel.plain t)
    (hng : ∀ o : OpFull, TxnOp.get o ∉ t.thenOps ++ t.elseOps)
    (hc : ∀ c ∈ t.cmps, c.rangeEnd ≠ [W8 0])
    (hd : ∀ o : OpFull, TxnOp.delete o ∈ t.thenOps ++ t.elseOps → o.base.rangeEnd ≠ [W8 0]) :
    txnNoZeroEnd (txnWireOf t) := by
  have hops : ∀ ops : List TxnOp, (∀ op ∈ ops, TxnOp.plain op) →
      (∀ o, TxnOp.get o ∉ ops) → (∀ o, TxnOp.delete o ∈ ops → o.base.rangeEnd ≠ [W8 0]) →
      txnOpsNoZeroEnd (ops.map opWire) := by
    intro ops
    induction ops with
    | nil => intros; trivial
    | cons op ops ih =>
      intro hp' hg hd'
      simp only [List.map_cons, txnOpsNoZeroEnd]
      refine ⟨?_, ih (fun o ho => hp' o (List.mem_cons_of_mem _ ho))
        (fun o ho => hg o (List.mem_cons_of_mem _ ho))
        (fun o ho => hd' o (List.mem_cons_of_mem _ ho))⟩
      cases op with
      | get o => exact absurd List.mem_cons_self (hg o)
      | delete o =>
        simp only [opWire, txnOpNoZeroEnd]
        rw [(deleteWire_key o).2]
        exact hd' o List.mem_cons_self
      | txn _ _ _ => exact (hp' _ List.mem_cons_self).elim
      | put _ _ _ => simp [opWire, txnOpNoZeroEnd]
      | putKeep _ _ => simp [opWire, txnOpNoZeroEnd]
      | putIgnVal _ _ => simp [opWire, txnOpNoZeroEnd]
  refine ⟨hc, hops _ hp.1 (fun o ho => hng o (List.mem_append_left _ ho))
    (fun o ho => hd o (List.mem_append_left _ ho)),
    hops _ hp.2 (fun o ho => hng o (List.mem_append_right _ ho))
    (fun o ho => hd o (List.mem_append_right _ ho))⟩

theorem noZeroEnd_wire (t : TxnModel) (hp : TxnModel.plain t)
    (hng : ∀ o : OpFull, TxnOp.get o ∉ t.thenOps ++ t.elseOps)
    (hc : ∀ c ∈ t.cmps, c.rangeEnd ≠ [W8 0])
    (hd : ∀ o : OpFull, TxnOp.delete o ∈ t.thenOps ++ t.elseOps → o.base.rangeEnd ≠ [W8 0]) :
    ∀ tw : txn.TxnModelW, tw.toModel = txnWireOf t → irrNoZeroEnd (irrTxn tw) := by
  intro tw htw
  refine ⟨fun o h => by simp [irrTxn, apply.irrEmpty] at h,
    fun o h => by simp [irrTxn, apply.irrEmpty] at h, fun t' h => ?_⟩
  simp only [irrTxn_txn, Option.some.injEq] at h
  subst h
  rw [htw]
  exact txnNoZeroEnd_wire0 t hp hng hc hd

section applied
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

/-- **A transaction's log**: its run's changes committed at the log the entry met (nothing
committed if there are none). -/
theorem txn_applied_exact (tw : txn.TxnModelW) (t' : TxnModel) (hm : apply.HeaderModel) (rq' : apply.IRRModel)
    (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool)
    (hw : irrWireOf (apply.withHeader (irrTxn tw) hm) rq') (ht : rq'.txn = some t')
    (h : apply.applyStep rq' true x x' (.dispatched (.applied l false) skip)) :
    x'.log = mvcc.commitLog x.log
      (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').2.1 := by
  have hk : apply.dispatchKind rq' = .txn := by
    rw [hw.2.2.1]
    simp [apply.dispatchKind, apply.withHeader, irrTxn, apply.irrEmpty]
  obtain ⟨-, hd, hl, -⟩ := h
  rw [hl]
  unfold apply.dispatchStep at hd
  rw [hk] at hd
  simp only [apply.preV3Kind, apply.storeKind, Bool.false_eq_true, ↓reduceIte,
    false_or] at hd
  have hb := v3rpc.chainStep_applied_false x.chain hd
  unfold apply.backendStep at hb
  rw [hk] at hb
  obtain ⟨t'', ht'', ⟨hb, -⟩ | ⟨hb, -⟩⟩ := hb
  · cases hb
  · rw [ht] at ht''
    cases ht''
    cases hb
    rfl

end applied

/-! ## The response -/

section resp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [EM : EtcdModel GF]

omit EM in
/-- **The reply's message of an operation answers it in the client's terms** (`txnOpRespAt`):
for a plain operation of the model whose wire operation the message answers (`opRespRel`); a get
with its ranges executed (`skip = false`) and `getExact` (the server answers it as the model
says). -/
theorem txnOpRespAt_of (skip : Bool) (p : Loc) (op : TxnOp) (res : TxnOpResult) (m : OpRespM)
    (hp : TxnOp.plain op) (hg : ∀ o, op = .get o → skip = false ∧ o.getExact)
    (hrel : opRespRel skip (opWire op) res m) :
    opRespMsg (GF := GF) p m ⊢ txnOpRespAt p op res := by
  cases op with
  | txn cs ts es => exact hp.elim
  | get o =>
    obtain ⟨hs, hx⟩ := hg o rfl
    cases res with
    | range sel n =>
      cases m with
      | range rev kvs more count =>
        simp only [opWire, opRespRel, hs, Bool.false_eq_true, ↓reduceIte] at hrel
        obtain ⟨hc, kvs', hok, hk⟩ := hrel
        rw [wire_fastKeysOnly o hx] at hk
        have hk' : kvs = kvs' := by
          rw [hk]; conv => rhs; rw [← List.map_id kvs']
          congr 1
        subst hk'
        have hok' := wire_rangeKvsOk o hx _ _ hok
        iintro #H
        iunfold opRespMsg at H
        icases H with ⟨%Hpn, %w, %r, #Hu, #Hw, #Hr⟩
        iunfold txn.rangeResponseIs at Hr
        icases Hr with ⟨%Hrn, %h, %sl, %ps, #Hh, %Hhn, #Hrev, #Hsl, #Hps, #Hkvs, -, #Hcount⟩
        iunfold txnOpRespAt
        isplitl []
        · ipureintro; exact Hpn
        iexists _
        iframe Hu
        iexists w, r
        isplitl []
        · ipureintro; rfl
        iframe Hw
        isplitl []
        · ipureintro; exact Hrn
        iunfold rangeRespAt
        iexists sl, ps, kvs
        iframe Hsl Hps
        isplitl []
        · iapply kvPtrsAt_of_kvsIs $$ Hkvs
        isplitl []
        · ipureintro; exact hok'
        rw [← hc]
        iframe Hcount
        iexists h, rev
        iframe Hh Hrev
        ipureintro; exact Hhn
      | _ => simp [opWire, opRespRel] at hrel
    | _ => cases m <;> simp [opWire, opRespRel] at hrel
  | delete o =>
    cases res with
    | delete n =>
      cases m with
      | delete rev d prevs =>
        simp only [opWire, opRespRel] at hrel
        subst hrel
        iintro #H
        iunfold opRespMsg at H
        icases H with ⟨%Hpn, %w, %r, #Hu, #Hw, %Hrn, %h, %sl, %ps, #Hh, %Hhn, #Hrev, #Hd, -⟩
        iunfold txnOpRespAt
        isplitl []
        · ipureintro; exact Hpn
        iexists _
        iframe Hu
        iexists w, r
        isplitl []
        · ipureintro; rfl
        iframe Hw Hd
        ipureintro; exact Hrn
      | _ => simp [opWire, opRespRel] at hrel
    | _ => cases m <;> simp [opWire, opRespRel] at hrel
  | put k v l =>
    cases res with
    | put =>
      cases m with
      | put rev prev =>
        iintro #H
        iunfold opRespMsg at H
        icases H with ⟨%Hpn, %w, %r, #Hu, #Hw, #Hr⟩
        iunfold txn.putResponseIs at Hr
        icases Hr with ⟨%Hrn, -⟩
        iunfold txnOpRespAt
        isplitl []
        · ipureintro; exact Hpn
        iexists _
        iframe Hu
        iexists w, r
        isplitl []
        · ipureintro; rfl
        iframe Hw
        ipureintro; exact Hrn
      | _ => simp [opWire, opRespRel] at hrel
    | _ => cases m <;> simp [opWire, opRespRel] at hrel
  | putKeep k v =>
    cases res with
    | put =>
      cases m with
      | put rev prev =>
        iintro #H
        iunfold opRespMsg at H
        icases H with ⟨%Hpn, %w, %r, #Hu, #Hw, #Hr⟩
        iunfold txn.putResponseIs at Hr
        icases Hr with ⟨%Hrn, -⟩
        iunfold txnOpRespAt
        isplitl []
        · ipureintro; exact Hpn
        iexists _
        iframe Hu
        iexists w, r
        isplitl []
        · ipureintro; rfl
        iframe Hw
        ipureintro; exact Hrn
      | _ => simp [opWire, opRespRel] at hrel
    | _ => cases m <;> simp [opWire, opRespRel] at hrel
  | putIgnVal k l =>
    cases res with
    | put =>
      cases m with
      | put rev prev =>
        iintro #H
        iunfold opRespMsg at H
        icases H with ⟨%Hpn, %w, %r, #Hu, #Hw, #Hr⟩
        iunfold txn.putResponseIs at Hr
        icases Hr with ⟨%Hrn, -⟩
        iunfold txnOpRespAt
        isplitl []
        · ipureintro; exact Hpn
        iexists _
        iframe Hu
        iexists w, r
        isplitl []
        · ipureintro; rfl
        iframe Hw
        ipureintro; exact Hrn
      | _ => simp [opWire, opRespRel] at hrel
    | _ => cases m <;> simp [opWire, opRespRel] at hrel

omit EM in
/-- **The reply's messages of the operations answer them in the client's terms** (in order). -/
theorem txnOpRespsAt_of (skip : Bool) :
    ∀ (ps : List Loc) (ops : List TxnOp) (rs : List TxnOpResult) (ms : List OpRespM),
    (∀ op ∈ ops, TxnOp.plain op ∧ ∀ o, op = .get o → skip = false ∧ o.getExact) →
    opRespsRel skip (ops.map opWire) rs ms →
    opRespsMsg (GF := GF) ps ms ⊢ ⌜ps.length = ops.length ∧ rs.length = ops.length⌝ ∗
      □ ∀ (i : Nat) (p : Loc) (op : TxnOp) (res : TxnOpResult), ⌜ps[i]? = some p⌝ -∗
        ⌜ops[i]? = some op⌝ -∗ ⌜rs[i]? = some res⌝ -∗ txnOpRespAt p op res
  | ps, [], [], [], _, _ => by
    cases ps with
    | nil =>
      iintro -
      isplitl []
      · ipureintro; simp
      iintro !> %i %p %op %res %h1
      simp at h1
    | cons p ps =>
      simp only [opRespsMsg]
      iintro H
      iexfalso; iexact H
  | ps, op :: ops, res :: rs, m :: ms, hops, hrel => by
    simp only [List.map_cons, opRespsRel] at hrel
    obtain ⟨hr0, hr1⟩ := hrel
    have h0 := hops op List.mem_cons_self
    cases ps with
    | nil =>
      simp only [opRespsMsg]
      iintro H
      iexfalso; iexact H
    | cons p ps =>
      simp only [opRespsMsg]
      iintro ⟨#H0, #H1⟩
      ihave #Hh := txnOpRespAt_of skip p op res m h0.1 h0.2 hr0 $$ H0
      ihave ⟨%Hl, #Ht⟩ := txnOpRespsAt_of skip ps ops rs ms
        (fun o ho => hops o (List.mem_cons_of_mem _ ho)) hr1 $$ H1
      isplitl []
      · ipureintro; simp [Hl.1, Hl.2]
      iintro !> %i %p' %op' %res' %h1 %h2 %h3
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2 h3
        subst h1 h2 h3
        iexact Hh
      | succ i =>
        simp only [List.getElem?_cons_succ] at h1 h2 h3
        iapply Ht $$ %i %p' %op' %res' %h1 %h2 %h3
  | _, [], [], _ :: _, _, h | _, [], _ :: _, _, _, h | _, _ :: _, [], _, _, h
  | _, _ :: _, _ :: _, [], _, h => by
    simp [opRespsRel] at h

omit EM in
/-- **The reply's message is the client's response** (`txnRespAt`): its header's revision, its
verdict, and the responses of the chosen branch's operations. -/
theorem txnRespAt_of_msg (skip : Bool) (resp : Loc) (m : TxnRespM) (r : w64) (ok : Bool)
    (ops : List TxnOp) (rs : List TxnOpResult) (h1 : m.hdr.revision = r) (h2 : m.succeeded = ok)
    (hops : ∀ op ∈ ops, TxnOp.plain op ∧ ∀ o, op = .get o → skip = false ∧ o.getExact)
    (hrel : opRespsRel skip (ops.map opWire) rs m.resps) :
    txnRespMsg (GF := GF) resp m ⊢ txnRespAt resp r ok ops rs := by
  iintro #H
  iunfold txnRespMsg at H
  icases H with ⟨%Hrn, %h, %sl, %ps, #Hh, #Hhf, #Hok, #Hsl, #Hps, #Hrs⟩
  iunfold hdrFull at Hhf
  icases Hhf with ⟨%Hhn, -, -, #Hrev, -, -⟩
  ihave ⟨%Hl, #Ht⟩ := txnOpRespsAt_of skip ps ops rs m.resps hops hrel $$ Hrs
  iunfold txnRespAt
  iexists h, sl, ps
  rw [← h1, ← h2]
  iframe Hh Hrev Hok Hsl Hps Ht
  isplitl []
  · ipureintro; exact Hhn
  ipureintro; exact Hl

end resp

theorem runOps_gets_noWrite (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), (∀ op ∈ ops, TxnOp.isGet op = true) →
      txnWrote (runOps r s ops).2 = false
  | s, [], _ => rfl
  | s, op :: ops, h => by
    have h0 := h op List.mem_cons_self
    have ih := runOps_gets_noWrite r (applyTxnOp r s op).1 ops
      (fun o ho => h o (List.mem_cons_of_mem _ ho))
    simp only [runOps, txnWrote, List.any_cons, Bool.or_eq_false_iff] at ih ⊢
    refine ⟨?_, ih⟩
    cases op <;> simp_all [TxnOp.isGet, applyTxnOp, TxnOpResult.wrote]

/-- Without nested transactions, the server's transaction is the client's (as in the txn
package's `Results.lean`, which no proof imports). -/
theorem srvRunTxn_runTxn_flat (r : w64) (s : List EtcdKv) (t : TxnModel)
    (h : txn.opsFlat (t.branch (txn.txnOk s t))) :
    (txn.srvRunTxn r s t).1 = (runTxn r s t).1 ∧
      mvcc.applyChanges r s (txn.srvRunTxn r s t).2.1 = (runTxn r s t).2.1 ∧
      (txn.srvRunTxn r s t).2.2 = (runTxn r s t).2.2 :=
  txn.srvRunTxn_runTxn r s t (txn.opsStable_flat s r s _ h)

theorem branch_mem (t : TxnModel) (ok : Bool) (op : TxnOp) (h : op ∈ t.branch ok) :
    op ∈ t.thenOps ++ t.elseOps := by
  cases ok
  · exact List.mem_append_right _ h
  · exact List.mem_append_left _ h

theorem plain_branch (t : TxnModel) (hp : TxnModel.plain t) (ok : Bool) :
    ∀ op ∈ t.branch ok, TxnOp.plain op := fun op h => by
  cases ok
  · exact hp.2 op h
  · exact hp.1 op h

theorem flat_branch (t : TxnModel) (hp : TxnModel.plain t) (ok : Bool) :
    txn.opsFlat (t.branch ok) := fun op h cs ts es he => by
  subst he; exact plain_branch t hp ok _ h

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **What a transaction's reply gives the clients' model** (`txnReplied` with its update's floor,
unit W-M3: if the transaction is linearizable, the state its update fired at, the state of the
log read or met, is at least a certified log `lf` longer than `lo`; for a transaction of plain
operations under `pfx` that is `exactGets`): `txnCommitResultTok`, the token iff it wrote. -/
theorem txnCommitResultTok_of_reply (E : apply.AEnv GF) (γw γr : ReadNames) (c : w64)
    (F : mvcc.Log) (lo : w64) (pfx : GoString) (t : TxnModel) (cid mid : w64) (resp : Loc)
    (m : TxnRespM) (Q : KVState → IProp GF) (lf : mvcc.Log) (hp : TxnModel.plain t)
    (hu : t.Under pfx) (hx : t.exactGets) (hlo : sint.Z lo < lf.length) :
    storeSmall E.γ ∗ txnRespMsg resp m ∗ txnReplied E γw γr c F (txnWireOf t) Q cid mid m ∗
        □ (⌜t.linearizable = true⌝ -∗ ∀ σ, Q σ -∗ ⌜lf.length ≤ σ.rev + 1⌝) ⊢
      txnCommitResultTok (EM := v3rpc.etcdModelOfServer E) pfx lo t resp GoInterface.nil := by
  iintro ⟨#Hsm, #Hm, Hrep, #Himp⟩
  unfold txnReplied
  have hser := txnSerializable_wire t
  rw [txnReadonly_wire]
  cases hro : (t.thenOps ++ t.elseOps).all TxnOp.isGet with
  | true =>
    simp only [↓reduceIte]
    icases Hrep with ⟨%log, #Hcert, #Hcok, %Hlog, -, #HQl⟩
    obtain ⟨h2, h3, hFl, hrev, -, -, hok, hrel⟩ := Hlog
    ihave %Hfl : ⌜t.linearizable = true → lf.length ≤ log.length⌝ $$ []
    · cases hlin : t.linearizable
      · ipureintro; intro h; cases h
      · ihave #Himp' := Himp $$ %rfl %(kvStateOf log)
        rw [hlin] at hser
        simp only [Bool.not_true] at hser
        simp only [hser, Bool.false_eq_true, ↓reduceIte]
        ihave %h := Himp' $$ HQl
        ipureintro; intro _
        simp only [kvStateOf_rev, kvStateOf_kvs] at h
        omega
    iclear HQl
    have hall : ∀ op ∈ t.thenOps ++ t.elseOps, TxnOp.isGet op = true := fun op ho =>
      List.all_eq_true.1 hro op ho
    have hnr : ∀ ok, ∀ op ∈ t.branch ok, TxnOp.noRev op := by
      intro ok op hop
      have := hall op (branch_mem t ok op hop)
      cases op <;> simp_all [TxnOp.isGet, TxnOp.noRev]
    have hw := srvRunTxn_wire (W64 (log.length : Int)) (mvcc.stateAfter log) t hp
    have hfl := srvRunTxn_runTxn_flat (W64 (log.length : Int)) (mvcc.stateAfter log) t
      (flat_branch t hp _)
    have hrr : runTxn (W64 ((log.length : Int) - 1)) (mvcc.stateAfter log) t =
        runTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t := by
      unfold runTxn
      simp only
      rw [runOps_noRev _ (W64 (log.length : Int)) _ _ (hnr _)]
    have hU := runTxn_underPfx pfx (W64 ((log.length : Int) - 1)) (mvcc.stateAfter log) t
      (mvcc.stateAfter_sorted log) hp hu
    rw [hw] at hok hrel
    have hok' : m.succeeded = (runTxn (W64 ((log.length : Int) - 1)) (mvcc.stateAfter log) t).1 := by
      rw [hrr, hok, hfl.1]
    have hrs : (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 =
        (runTxn (W64 ((log.length : Int) - 1)) (mvcc.stateAfter log) t).2.2 := by
      rw [hrr, hfl.2.2]
    rw [hrs, txnWireOf_branch, hok'] at hrel
    have hnw : txnWrote (runTxn (W64 ((log.length : Int) - 1)) (mvcc.stateAfter log) t).2.2 =
        false := by
      unfold runTxn
      exact runOps_gets_noWrite _ _ _ (fun op ho => hall op (branch_mem t _ op ho))
    have hr : sint.Z (W64 ((log.length : Int) - 1)) = (log.length : Int) - 1 := by word
    ihave ⟨#Hst, %Hwf⟩ := v3rpc.etcdState_of_cert_last E log pfx h2 h3 $$ [$Hsm $Hcert]
    unfold txnCommitResultTok
    iright
    isplitl []
    · ipureintro; rfl
    iexists (W64 ((log.length : Int) - 1)), (txn.underPfx pfx (mvcc.stateAfter log))
    rw [hU]
    simp only [hnw, Bool.false_eq_true, ↓reduceIte]
    isplitl []
    · iapply txnRespAt_of_msg false resp m _ _ _ _ hrev hok'
        (fun op ho => ⟨plain_branch t hp _ op ho, fun o he => by
          subst he; exact ⟨rfl, (hx.1 o (branch_mem t _ _ ho)).2⟩⟩) hrel $$ Hm
    isplitl []
    · iapply v3rpc.etcdReached_of_certOk E log _ (by rw [hr]; omega) $$ Hcok
    isplitl []
    · ipureintro
      exact ⟨fun h => by have := Hfl h; rw [hr]; omega, by rw [hr]; omega, by rw [hr]; omega, Hwf⟩
    isplitl []
    · unfold txnStates
      simp only [hnw, Bool.false_eq_true, ↓reduceIte]
      iexact Hst
    itrivial
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hgx, hwx⟩ := hx
    obtain ⟨hng, hcz, hdz⟩ := hwx hro
    icases Hrep with ⟨%tw, %hm, %rq', %t', %x, %x', %l, %skip, %Hp, #Hcert, HMint, -, #Hcok, HQ⟩
    obtain ⟨Htw, Hw, Ht', Hz, Hst, hrev, -, -, HF, H2, H4, hok, hrel, -⟩ := Hp
    have hlin : t.linearizable = true :=
      linearizable_of_write t (by rw [txnReadonly_wire]; exact hro)
    ihave %Hfl := Himp $$ %hlin %(kvStateOf x.log) HQ
    have ht' : t' = txnWireOf t := Hz (noZeroEnd_wire t hp hng hcz hdz tw Htw)
    subst ht'
    have hlog := txn_applied_exact tw (txnWireOf t) hm rq' x x' l skip Hw Ht' Hst
    have hw := srvRunTxn_wire (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t hp
    rw [hw] at hlog hok hrel hrev
    have hfl := srvRunTxn_runTxn_flat (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t (flat_branch t hp _)
    have hS := mvcc.stateAfter_sorted x.log
    have hFl : lf.length ≤ x.log.length := by simp only [kvStateOf_rev, kvStateOf_kvs] at Hfl; omega
    have hnil := srvOps_changes_nil (mvcc.stateAfter x.log) (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) _ (plain_branch t hp (txn.txnOk (mvcc.stateAfter x.log) t))
    by_cases hcs : (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t).2.1 = []
    · -- nothing written: the log as it was, the revision its last
      have hwr : txnWrote (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t).2.2 = false := hnil.1 hcs
      have hnr := srvOps_notWrote_noRev (mvcc.stateAfter x.log) (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) _ (plain_branch t hp (txn.txnOk (mvcc.stateAfter x.log) t)) hwr
      have hrr : runTxn (W64 ((x.log.length : Int) - 1)) (mvcc.stateAfter x.log) t = runTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t := by
        unfold runTxn
        simp only
        rw [runOps_noRev _ (W64 (x.log.length : Int)) _ _ hnr]
      have hU := runTxn_underPfx pfx (W64 ((x.log.length : Int) - 1)) (mvcc.stateAfter x.log) t hS hp hu
      have hok' : m.succeeded = (runTxn (W64 ((x.log.length : Int) - 1)) (mvcc.stateAfter x.log) t).1 := by
        rw [hrr, hok, hfl.1]
      have hrs : (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t).2.2 = (runTxn (W64 ((x.log.length : Int) - 1)) (mvcc.stateAfter x.log) t).2.2 := by
        rw [hrr, hfl.2.2]
      rw [hrs, txnWireOf_branch, hok'] at hrel
      rw [hrs] at hwr
      have hrev' : m.hdr.revision = W64 ((x.log.length : Int) - 1) := by
        rw [hrev, mvcc.writeRev, if_pos hcs]; congr 1; omega
      rw [hcs] at hlog
      simp only [mvcc.commitLog, ↓reduceIte] at hlog
      rw [hlog]
      have hr : sint.Z (W64 ((x.log.length : Int) - 1)) = (x.log.length : Int) - 1 := by word
      ihave ⟨#Hs1, %Hwf1⟩ := v3rpc.etcdState_of_cert_last E x.log pfx H2 (by omega) $$ [$Hsm $Hcert]
      unfold txnCommitResultTok
      iright
      isplitl []
      · ipureintro; rfl
      iexists (W64 ((x.log.length : Int) - 1)), (txn.underPfx pfx (mvcc.stateAfter x.log))
      rw [hU]
      simp only [hwr, Bool.false_eq_true, ↓reduceIte]
      isplitl []
      · iapply txnRespAt_of_msg skip resp m _ _ _ _ hrev' hok'
          (fun op ho => ⟨plain_branch t hp _ op ho, fun o he => by
            subst he; exact absurd (branch_mem t _ _ ho) (hng o)⟩) hrel $$ Hm
      isplitl []
      · iapply v3rpc.etcdReached_of_certOk E x.log _ (by rw [hr]; omega) $$ Hcok
      isplitl []
      · ipureintro
        exact ⟨fun _ => by rw [hr]; omega, by rw [hr]; omega, by rw [hr]; omega, Hwf1⟩
      isplitl []
      · unfold txnStates
        simp only [hwr, Bool.false_eq_true, ↓reduceIte]
        iexact Hs1
      itrivial
    · -- written: the log's next revision, with its token
      have hwr : txnWrote (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t).2.2 = true := by
        cases h : txnWrote (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t).2.2
        · exact absurd (hnil.2 h) hcs
        · rfl
      have hU := runTxn_underPfx pfx (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t hS hp hu
      have hok' : m.succeeded = (runTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t).1 := by rw [hok, hfl.1]
      have hrs : (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t).2.2 = (runTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t).2.2 := hfl.2.2
      rw [hrs, txnWireOf_branch, hok'] at hrel
      rw [hrs] at hwr
      have hrev' : m.hdr.revision = (W64 (x.log.length : Int)) := by
        rw [hrev, mvcc.writeRev, if_neg hcs]
      have hlog' : x'.log = x.log ++ [(txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t).2.1] := by
        rw [hlog, mvcc.commitLog, if_neg hcs]
      have hr : sint.Z (W64 (x.log.length : Int)) = x.log.length := by word
      have hr1 : sint.Z ((W64 (x.log.length : Int)) - W64 1) = (x.log.length : Int) - 1 := by word
      ihave #Hst1 := v3rpc.etcdState_of_cert E x'.log ((W64 (x.log.length : Int)) - W64 1) pfx
        (by rw [hr1]; omega) (by rw [hr1, hlog']; simp; omega) $$ [$Hsm $Hcert]
      ihave #Hst2 := v3rpc.etcdState_of_cert E x'.log (W64 (x.log.length : Int)) pfx
        (by rw [hr]; omega) (by rw [hr, hlog']; simp; omega) $$ [$Hsm $Hcert]
      icases Hst1 with ⟨#Hs1, %Hwf1⟩
      icases Hst2 with ⟨#Hs2, -⟩
      have e1 : mvcc.stateAt x'.log (sint.Z ((W64 (x.log.length : Int)) - W64 1)).toNat = (mvcc.stateAfter x.log) := by
        rw [hr1, hlog', show ((x.log.length : Int) - 1).toNat = x.log.length - 1 by omega,
          mvcc.stateAt_append_lt _ _ (by omega), mvcc.stateAt_last]
      have e2 : mvcc.stateAt x'.log (sint.Z (W64 (x.log.length : Int))).toNat = (runTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t).2.1 := by
        rw [hr, show ((x.log.length : Int)).toNat = x'.log.length - 1 by rw [hlog']; simp,
          mvcc.stateAt_last, hlog', mvcc.stateAfter_append, ← hfl.2.1]
      rw [e1] at Hwf1
      unfold txnCommitResultTok
      iright
      isplitl []
      · ipureintro; rfl
      iexists (W64 (x.log.length : Int)), (txn.underPfx pfx (mvcc.stateAfter x.log))
      rw [hU]
      simp only [hwr, ↓reduceIte]
      isplitl []
      · iapply txnRespAt_of_msg skip resp m _ _ _ _ hrev' hok'
          (fun op ho => ⟨plain_branch t hp _ op ho, fun o he => by
            subst he; exact absurd (branch_mem t _ _ ho) (hng o)⟩) hrel $$ Hm
      isplitl []
      · iapply v3rpc.etcdReached_of_certOk E x'.log _ (by rw [hr, hlog']; simp; omega) $$ Hcok
      isplitl []
      · ipureintro
        exact ⟨fun _ => by rw [hr]; omega, by rw [hr]; omega, by rw [hr]; omega, Hwf1⟩
      isplitl []
      · unfold txnStates
        simp only [↓reduceIte]
        isplitl
        · rw [← e1]; iexact Hs1
        · rw [← e2]; iexact Hs2
      iunfold revMinted at HMint
      icases HMint with (%He | ⟨%cs, %He, Htok⟩)
      · rw [hlog'] at He
        exact absurd (congrArg List.length He) (by simp)
      rw [v3rpc.etcdModelOfServer_etcdRevToken]
      iexact Htok

/-! ## Transactions in the KV model (2026-10-15, unit T2) -/

/-- An operation that names no lease (`0`) and keeps none (no `IgnoreLease`). -/
def TxnOp.leaseFree : TxnOp → Prop
  | .put _ _ l => l = W64 0
  | .putIgnVal _ l => l = some (W64 0)
  | .putKeep _ _ => False
  | _ => True

/-- **A transaction with no lease** (every operation of both branches `leaseFree`): with
`exactGets`, its wire's transaction is plain in the KV model (`txnPlain_wire`). -/
def TxnModel.leaseFree (t : TxnModel) : Prop := ∀ op ∈ t.thenOps ++ t.elseOps, TxnOp.leaseFree op

theorem opsPlain_wire (ops : List TxnOp)
    (h : ∀ op ∈ ops, TxnOp.plain op ∧ TxnOp.leaseFree op ∧ ∀ o, op = .get o → o.base.rev = W64 0) :
    txn.opsPlain (ops.map opWire) := by
  induction ops with
  | nil => simp [txn.opsPlain]
  | cons op ops ih =>
    simp only [List.map_cons, txn.opsPlain]
    refine ⟨?_, ih (fun op' h' => h op' (List.mem_cons_of_mem _ h'))⟩
    obtain ⟨hp, hl, hg⟩ := h op List.mem_cons_self
    cases op with
    | get o => simp only [opWire, txn.opPlain]; rw [(wire_fields o).2.2.1]; exact hg o rfl
    | delete o => simp [opWire, txn.opPlain]
    | txn _ _ _ => exact hp.elim
    | put k v l => simpa [opWire, txn.opPlain, TxnOp.leaseFree] using hl
    | putKeep k v => exact hl.elim
    | putIgnVal k l => simpa [opWire, txn.opPlain, TxnOp.leaseFree] using hl

/-- **A plain lease-free transaction with exact gets is plain in the KV model** on the wire. -/
theorem txnPlain_wire (t : TxnModel) (hp : TxnModel.plain t) (hx : t.exactGets)
    (hl : TxnModel.leaseFree t) : txn.txnPlain (txnWireOf t) := by
  have h : ∀ op ∈ t.thenOps ++ t.elseOps,
      TxnOp.plain op ∧ TxnOp.leaseFree op ∧ ∀ o, op = .get o → o.base.rev = W64 0 := by
    intro op hop
    refine ⟨?_, hl op hop, fun o he => (hx.1 o (he ▸ hop)).1⟩
    rcases List.mem_append.1 hop with h | h
    · exact hp.1 op h
    · exact hp.2 op h
  exact ⟨opsPlain_wire _ (fun op h' => h op (List.mem_append_left _ h')),
    opsPlain_wire _ (fun op h' => h op (List.mem_append_right _ h'))⟩

/-- **A writing transaction with exact gets has no range end `[0]`** on the wire. -/
theorem txnNoZeroEnd_wire (t : TxnModel) (hp : TxnModel.plain t) (hx : t.exactGets)
    (hw : txn.txnReadonly (txnWireOf t) = false) : txnNoZeroEnd (txnWireOf t) := by
  rw [txnReadonly_wire] at hw
  obtain ⟨hng, hc, hd⟩ := hx.2 hw
  exact txnNoZeroEnd_wire0 t hp hng hc hd

/-! ## The builder -/

theorem txnModelIn_wire (t : TxnModel) (hx : t.exactGets) : txnModelIn (txnWireOf t) := by
  intro o ho
  simp only [txnWireOf, ← List.map_append, List.mem_map] at ho
  obtain ⟨op, hop, he⟩ := ho
  cases op with
  | get o' =>
    simp only [opWire, TxnOp.get.injEq] at he
    subst he
    obtain ⟨hr, hgx⟩ := hx.1 o' hop
    exact ⟨by rw [(wire_fields o').2.2.1]; exact hr, wire_not_cutEarly o' hgx⟩
  | delete _ => simp [opWire] at he
  | txn _ _ _ => simp [opWire] at he
  | put _ _ _ => simp [opWire] at he
  | putKeep _ _ => simp [opWire] at he
  | putIgnVal _ _ => simp [opWire] at he

theorem plain_append_ops (os : List OpFull) (ops : List TxnOp)
    (h : os.map txnOpOf = ops.map some) : ∀ op ∈ ops, TxnOp.plain op := by
  intro op hop
  have : some op ∈ os.map txnOpOf := by rw [h]; exact List.mem_map_of_mem hop
  obtain ⟨o, -, ho⟩ := List.mem_map.1 this
  exact txnOpOf_plain o op ho

/-- The builder's interface value (a `*txn` as a `Txn`). -/
abbrev txnIfaceOf (tp : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp

/-- The builder's abstract state (`txnBuilderSpecX`'s `B`): the `*txn`'s fields at a quiet
context, its operations plain. -/
def txnB (tp : Loc) (addr : List GoString) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild) :
    IProp GF :=
  iprop(txnObjAt tp addr todoCtxVal cd b ∗ ⌜TxnModel.plain b.model⌝)

theorem etcdReached_zero (E : apply.AEnv GF) :
    ⊢ etcdReached (EM := v3rpc.etcdModelOfServer E) (W64 0) := by
  unfold etcdReached
  ileft
  ipureintro; exact Int.le_refl _

/-- **A writing transaction with a lease, its `Commit()`** (a premise, persistent; 2026-10-15, unit
T2: leases are outside the KV model until unit T3, so no server spec covers a writing transaction
with a lease). Unit W-M3: stated in the clients' model, as `kvLeasedPutTodo` (a writing
transaction is linearizable, and its floor, for a lease-free one its update's result at the state
of the log it met, has no counterpart without an update): `txnCommitResultTok` from
`etcdReached lo` under a prefix, with a client error; and, for the builder's commit with any
result, `txnAnyResult`. -/
def kvLeasedCommitTodo (E : apply.AEnv GF) (_γw _γr : ReadNames) (_cid _mid : w64)
    (addr : List GoString) : IProp GF :=
  iprop(□ ∀ (tp : Loc) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild),
    ⌜TxnModel.plain b.model ∧ b.model.exactGets ∧ txn.txnReadonly (txnWireOf b.model) = false ∧
      ¬ TxnModel.leaseFree b.model⌝ -∗
    ((□ ∀ (lo : w64) (pfx : GoString), ⌜b.model.Under pfx⌝ -∗
      {{ txnObjAt tp addr ci cd b ∗ etcdReached (EM := v3rpc.etcdModelOfServer E) lo }}
        (App (Val #(methods (txnIfaceOf tp).ty go!"Commit" (txnIfaceOf tp).v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          txnCommitResultTok (EM := v3rpc.etcdModelOfServer E) pfx lo b.model resp err ∗
          (⌜err = GoInterface.nil⌝ ∨ ⌜err ≠ GoInterface.nil ∧ clientErr err⌝) }}) ∗
     {{ txnObjAt tp addr ci cd b }}
       (App (Val #(methods (txnIfaceOf tp).ty go!"Commit" (txnIfaceOf tp).v)) (Val #()))
     {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); txnAnyResult resp err }}))

instance kvLeasedCommitTodo_persistent (E : apply.AEnv GF) (γw γr : ReadNames) (cid mid : w64)
    (addr : List GoString) : Persistent (kvLeasedCommitTodo E γw γr cid mid addr) := by
  unfold kvLeasedCommitTodo; infer_instance

/-- **`Commit()` on a real builder, its call** (at a floor `F`, the committed index `0`; a read-only
or lease-free transaction): the reply's message with `txnReplied` at the update the call chose,
or a client error. 2026-10-15 (unit T2): with the caller's update `kvAnyAu` (etcd's `Txn` spec over
the whole state). Unit W-M3: the update's result is the floor of a certified log `lf` (`kvAnyAu`):
a writing transaction's at the write names, a linearizable read-only one's read update at the
read names, none for a serializable one (which is not linearizable). -/
theorem kv_txn_commit (tp : Loc) (addr : List GoString) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (F lf : mvcc.Log) (hp : TxnModel.plain b.model) (hx : b.model.exactGets)
    (hk : txn.txnReadonly (txnWireOf b.model) = true ∨ TxnModel.leaseFree b.model) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
        kvRegs (srvsAt addr E γr cid mid) ∗
        mvcc.idxCert E.γ.idx F ∗ mvcc.certOk E.γ lf ∗ kvAnyAu E γr }}
      (App (Val #(methods (txnIfaceOf tp).ty go!"Commit" (txnIfaceOf tp).v)) (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (Q : KVState → IProp GF), txnRespMsg resp m ∗
            txnReplied E γr γr (W64 0) F (txnWireOf b.model) Q cid mid m ∗
            □ (⌜b.model.linearizable = true⌝ -∗ ∀ σ, Q σ -∗ ⌜lf.length ≤ σ.rev + 1⌝)) ∨
          ⌜err ≠ GoInterface.nil ∧ clientErr err⌝ }} := by
  iintro %Φ ⟨#Pc, Hobj, #Hrpc, #HF, #Hcl, #Hr⟩ HΦ
  ihave #Hw : kvAnyAu E γr $$ []
  · iexact Hr
  have hser := txnSerializable_wire b.model
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  ihave #Hc0 : committedAtLeast γr (W64 0) $$ []
  · unfold committedAtLeast
    rw [show uint.nat (W64 0) = 0 from rfl]
    iexact H0
  -- the update: a writing transaction's, a linearizable read-only one's read update, or none
  ihave Hsel : iprop(|={⊤}=> ∃ Q : KVState → IProp GF,
      (⌜txn.txnReadonly (txnWireOf b.model) = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly (txnWireOf b.model) = true ∧
          txn.txnSerializable (txnWireOf b.model) = false⌝ ∗ kvReadAu γr.kv Q) ∨
        (⌜txn.txnReadonly (txnWireOf b.model) = false ∧ txn.txnPlain (txnWireOf b.model) ∧
          txnNoZeroEnd (txnWireOf b.model)⌝ ∗ □ kvOpAu1 γr.kv (.txn (txnWireOf b.model)) Q)) ∗
      □ (⌜b.model.linearizable = true⌝ -∗ ∀ σ, Q σ -∗ ⌜lf.length ≤ σ.rev + 1⌝)) $$ []
  · cases hro : txn.txnReadonly (txnWireOf b.model)
    · have hl : TxnModel.leaseFree b.model := by
        rcases hk with h | h
        · rw [hro] at h; cases h
        · exact h
      iunfold kvAnyAu at Hw
      imod Hw $$ %(KVOp.txn (txnWireOf b.model)) %lf Hcl with #Hau
      imodintro
      -- (2026-10-20, linkv-txn stage A) the update fired at most once, its result persistent
      iexists (fun σ => iprop(□ ⌜lf.length ≤ σ.rev + 1⌝))
      isplitl
      · iright; iright
        isplitr
        · ipureintro; exact ⟨rfl, txnPlain_wire _ hp hx hl, txnNoZeroEnd_wire _ hp hx hro⟩
        iintro !>
        iapply kvOpAu_one $$ Hau
      · iintro !> - %σ #H; iexact H
    · cases hs : txn.txnSerializable (txnWireOf b.model)
      · iunfold kvAnyAu at Hr
        imod Hr $$ %(KVOp.range (opGetModel [] [])) %lf Hcl with #Hau
        imodintro
        iexists (fun σ => iprop(⌜lf.length ≤ σ.rev + 1⌝))
        isplitl
        · iright; ileft
          isplitr
          · ipureintro; exact ⟨rfl, rfl⟩
          iapply kvOpAu_range $$ Hau
        · iintro !> - %σ H; iexact H
      · imodintro
        iexists (fun _ => iprop(True))
        isplitl
        · ileft; ipureintro; exact ⟨rfl, rfl⟩
        · iintro !> %h
          rw [h] at hser; simp at hser; rw [hser] at hs; cases hs
  imod Hsel with ⟨%Q, #Hdq, #Himp⟩
  ihave #Hu : □ txnUpdAt γr γr (txnWireOf b.model) Q $$ []
  · icases Hdq with (%H | ⟨%H, #Ha⟩ | ⟨%H, #Ha⟩)
    · imodintro; iunfold txnUpdAt; ileft; ipureintro; exact H
    · imodintro; iunfold txnUpdAt; iright; ileft; iframe Ha; ipureintro; exact H
    · imodintro; iunfold txnUpdAt; iright; iright; iframe Ha; ipureintro; exact H
  ihave #Hus := txnUpd_srvsAt addr E γr cid mid (txnWireOf b.model) Q $$ Hu
  iapply (v3.txn.wp_CommitM tp (srvsAt addr E γr cid mid) ci cd b (W64 0) F Q) $$ [Hobj]
  · rw [srvsAt_addr]
    iframe
    iframe #
    isplitl []
    · ipureintro; exact ⟨hp, txnModelIn_wire _ hx⟩
    isplitl []
    · iapply knownAt_srvsAt $$ []
      iframe #
    iapply txnReqPre_box
    imodintro
    inext
    iexact Hus
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold txnCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, -⟩)
  · ihave Hq := txnAns_srvsAt addr E γr (W64 0) cid mid F _ Q m $$ Hq
    ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m, Q
    iframe
    iframe #
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.1⟩

/-- **A real `*kv` meets the recipes' transaction contract** (`isEtcdTxnKVTodo`) at the server's
model (see the file header). Premises: the registration of etcd's `Txn` at `addr`, the server's
read side (`isServerRead`), that `errors.As` can take `*rpctypes.EtcdError` (`hAs`), and that the
client's errors are client errors as `errors.Is` sees them (`clientErrsIs`). -/
theorem isEtcdTxnKVTodo_of_kv (api : Loc) (addr : List GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (pfx : GoString)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isServerRead s E γr ∗
        kvObjAt api addr ∗ kvRegs (srvsAt addr E γr cid mid) ∗
        clientErrsIs ∗ kvAnyAu E γr ∗ kvLeasedCommitTodo E γr γr cid mid addr ⊢
      isEtcdTxnKVTodo (EM := v3rpc.etcdModelOfServer E) (kvIfaceOf api) pfx := by
  iintro ⟨#Pc, #Hsrd, #Hkv, #Hrpc, #Hcei, #Hnr, #Hlc⟩
  ihave #Hsm := storeSmall_of_read s E γr $$ Hsrd
  unfold isEtcdTxnKVTodo
  iintro !> %Φ !> - HΦ
  imod (todo_ctx (GF := GF) hAs) with ⟨%cd, #Hctx, #Hce⟩
  iapply (v3.kv.wp_Txn api addr todoCtxVal cd) $$ []
  · iframe #
  inext
  iintro %t ⟨%tp, %Ht, Hobj, -⟩
  subst Ht
  iapply HΦ $$ %(txnIfaceOf tp)
  iexists (txnB tp addr cd)
  -- the commit at a floor, for both `Commit` triples
  have hcommit : ∀ (b : TxnBuild) (lo : w64), b.model.Under pfx → b.model.exactGets →
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isServerRead s E γr ∗
        kvRegs (srvsAt addr E γr cid mid) ∗ storeSmall E.γ ∗
        kvAnyAu E γr ∗ kvLeasedCommitTodo E γr γr cid mid addr ⊢
      {{ txnB tp addr cd b ∗ etcdReached (EM := v3rpc.etcdModelOfServer E) lo }}
        (App (Val #(methods (txnIfaceOf tp).ty go!"Commit" (txnIfaceOf tp).v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          txnCommitResultTok (EM := v3rpc.etcdModelOfServer E) pfx lo b.model resp err ∗
          (⌜err = GoInterface.nil⌝ ∨ ⌜err ≠ GoInterface.nil ∧ clientErr err⌝) }} := by
    intro b lo hu hx
    iintro ⟨#Pc, #Hsrd, #Hrpc, #Hsm, #Hnr, #Hlc⟩ !> %Φ ⟨HB, #Hlo⟩ HΦ
    iunfold txnB at HB
    icases HB with ⟨Hobj, %hp⟩
    by_cases hk : txn.txnReadonly (txnWireOf b.model) = true ∨ TxnModel.leaseFree b.model
    rotate_left
    · -- a writing transaction with a lease: the premise
      have hk1 : txn.txnReadonly (txnWireOf b.model) = false := by
        cases h : txn.txnReadonly (txnWireOf b.model)
        · rfl
        · exact absurd (Or.inl h) hk
      have hk2 : ¬ TxnModel.leaseFree b.model := fun h => hk (Or.inr h)
      iunfold kvLeasedCommitTodo at Hlc
      ihave ⟨#Ht, -⟩ := Hlc $$ %tp %todoCtxVal %cd %b %(⟨hp, hx, hk1, hk2⟩)
      ihave #Ht' := Ht $$ %lo %pfx %hu
      iapply Ht' $$ [Hobj] HΦ
      iframe Hobj Hlo
    -- the floor (unit W-M3): a certified log longer than `lo`, the update's result at the state
    -- the transaction linearized at
    ihave ⟨%lf, #Hcl, %Hll⟩ := certOk_of_reached E lo $$ Hlo
    ihave ⟨%F, #HF, -⟩ := floor0_of_read s E γr $$ Hsrd
    iapply (kv_txn_commit tp addr E γr cid mid todoCtxVal cd b F lf hp hx hk) $$ [Hobj]
    · iframe
      iframe #
    inext
    iintro %resp %err Hout
    iapply HΦ
    icases Hout with (⟨%Herr, %m, %Q, #Hm, Hq, #Himp⟩ | %Herr)
    · subst Herr
      isplitl
      · iapply txnCommitResultTok_of_reply E γr γr (W64 0) F lo pfx b.model cid mid resp m Q lf
          hp hu hx Hll $$ [$Hsm $Hm $Hq $Himp]
      · ileft; ipureintro; rfl
    · isplitl []
      · unfold txnCommitResultTok; ileft; ipureintro; exact Herr.1
      · iright; ipureintro; exact Herr
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
      iapply (hcommit b lo hux.1 hux.2) $$ [$Pc $Hsrd $Hrpc $Hsm $Hnr $Hlc] [HB]
      · iframe; iframe #
      inext
      iintro %resp %err ⟨Hr, -⟩
      iapply HΦ'
      iexact Hr
    · iintro !> %b %Φ' !> ⟨HB, %hx⟩ HΦ'
      iunfold txnB at HB
      icases HB with ⟨Hobj, %hp⟩
      by_cases hk : txn.txnReadonly (txnWireOf b.model) = true ∨ TxnModel.leaseFree b.model
      rotate_left
      · -- a writing transaction with a lease: the premise
        have hk1 : txn.txnReadonly (txnWireOf b.model) = false := by
          cases h : txn.txnReadonly (txnWireOf b.model)
          · rfl
          · exact absurd (Or.inl h) hk
        have hk2 : ¬ TxnModel.leaseFree b.model := fun h => hk (Or.inr h)
        iunfold kvLeasedCommitTodo at Hlc
        ihave ⟨-, #Ht⟩ := Hlc $$ %tp %todoCtxVal %cd %b %(⟨hp, hx, hk1, hk2⟩)
        iapply Ht $$ [Hobj] HΦ'
        iexact Hobj
      ihave ⟨%F, #HF, -⟩ := floor0_of_read s E γr $$ Hsrd
      ihave #Hcl : mvcc.certOk E.γ ([] : mvcc.Log) $$ []
      · unfold mvcc.certOk; ileft; ipureintro; simp
      iapply (kv_txn_commit tp addr E γr cid mid todoCtxVal cd b F [] hp hx hk) $$ [Hobj]
      · iframe
        iframe #
      inext
      iintro %resp %err Hout
      iapply HΦ'
      unfold txnAnyResult
      icases Hout with (⟨%Herr, %m, %Q, #Hm, -⟩ | %Herr)
      · iright
        isplitl []
        · ipureintro; exact Herr
        iunfold txnRespMsg at Hm
        icases Hm with ⟨%Hrn, %h, %sl, %ps, #Hh, -, #Hok, -⟩
        iexists h, m.succeeded
        iframe Hh Hok
      · ileft; ipureintro; exact Herr.1
  · unfold txnCommitErrTodo
    iintro !> %b %lo %Φ' !> ⟨HB, #Hlo, %hux⟩ HΦ'
    iapply (hcommit b lo hux.1 hux.2) $$ [$Pc $Hsrd $Hrpc $Hsm $Hnr $Hlc] [HB]
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

/-- **The clients' updates and the operations with a lease** (persistent; 2026-10-15, unit T2: it
replaces the merge M1's non-plain credit): any operation's update (`kvAnyAu`, which a client that
does not track etcd's abstract state has, `kvAnyAu_of_inv`; unit W-M3: with the floor of a
certified log, at the server's read names: since D44 one set, a started server's request path's
and read loop's being the same, `ρ.rd = γr`) and, until unit
T3, the
clients' triples of a put and of a writing transaction with a lease (`kvLeasedPutTodo`,
`kvLeasedCommitTodo`), which no server spec covers. -/
def kvWritesOk (api : Loc) (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) : IProp GF :=
  iprop(kvAnyAu E γr ∗ kvLeasedPutTodo api E ∗ kvLeasedCommitTodo E γr γr cid mid addr)

instance kvWritesOk_persistent (api : Loc) (addr : List GoString) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) : Persistent (kvWritesOk api addr E γr cid mid) := by
  unfold kvWritesOk; infer_instance

end proofs

end client
end EtcdGrove
end Perennial
