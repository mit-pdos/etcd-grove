/-
**A real `*kv`'s puts and deletes meet the recipes' contracts** at the server's model (the
vertical slice's unit V2, 2026-10-14; the shared part: `InvServerKV.lean`). Lean-first, no Rocq
counterpart.

* `isEtcdPutKVTodo_of_kv`: `kv.Put(context.TODO(), key, val, opts...)` on a `*kv` over a
  connection to a gRPC server at `addr` where etcd's `Put` is registered (`etcd_kv_served`)
  returns `putResult` in the server's model
  (`v3rpc.etcdModelOfServer E`): the put's revision `r` is the log's next (`|x.log|`), at least the
  caller's `lo` (unit W-M3: its update's floor, `kvAnyAu`, at the state of the log the put met,
  extends the certified log of `lo`, `certOk_of_reached`), with the token the apply thread minted
  for it;
  etcd's states at `r - 1` and `r` restricted to the prefix are the put's (`stateAfter_put`, the
  model's put commuting with the restriction to a prefix the key is under: `underPfx_putKv`).
* `isEtcdDeleteKVTodo_of_kv`: `kv.Delete(context.TODO(), key, opts...)` returns `deleteResult`:
  the delete's revision is the log's next if it deleted a key, the last otherwise
  (`mvcc.writeRev`), and etcd's states around it are the delete's
  (`stateAfter_commit_delete`, the delete commuting with the restriction to a prefix its range is
  under).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvServerKV

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
  mvcc txn

/-! ## The model: a write under a prefix commutes with the restriction to it -/

theorem find_underPfx (pfx k : GoString) (s : List EtcdKv) (h : pfx <+: k) :
    (underPfx pfx s).find? (fun v => decide (v.key = k)) =
      s.find? (fun v => decide (v.key = k)) := by
  unfold underPfx
  induction s with
  | nil => rfl
  | cons v vs ih =>
    by_cases hv : v.key = k
    · subst hv
      simp [List.filter_cons, h]
    · by_cases hp : pfx <+: v.key
      · simp [List.filter_cons, hp, hv, ih]
      · simp [List.filter_cons, hp, hv, ih]

theorem underPfx_putKv (pfx : GoString) (r : w64) (k v : GoString) (l : w64) (s : List EtcdKv)
    (hs : s.Pairwise etcdKvLess) (h : pfx <+: k) :
    underPfx pfx (putKv r k v l s) = putKv r k v l (underPfx pfx s) := by
  rw [putKv_eq, putKv_eq]
  unfold underPfx
  rw [filter_btInsert etcdKvLess_swo _ (pfx_respEquiv pfx) _ s hs]
  have hk : (putNv r k v l s).key = k := putNv_key r k v l s
  have hnv : putNv r k v l (s.filter fun v => decide (pfx <+: v.key)) = putNv r k v l s := by
    unfold putNv
    have := find_underPfx pfx k s h
    unfold underPfx at this
    rw [this]
  rw [hnv]
  simp [hk, h]

/-- A put-like operation (a put, a put keeping the lease or the value) under the prefix: the
model's run on the restriction is the restriction of its run. -/
theorem applyTxnOp_put_underPfx (pfx : GoString) (r : w64) (s : List EtcdKv)
    (hs : s.Pairwise etcdKvLess) (op : TxnOp) (hput : op.isGet = false)
    (hdel : ∀ o, op ≠ .delete o) (htxn : ∀ cs ts es, op ≠ .txn cs ts es) (hu : op.Under pfx) :
    applyTxnOp r (underPfx pfx s) op = (underPfx pfx (applyTxnOp r s op).1, (applyTxnOp r s op).2) := by
  cases op with
  | get o => simp [TxnOp.isGet] at hput
  | delete o => exact absurd rfl (hdel o)
  | txn cs ts es => exact absurd rfl (htxn cs ts es)
  | put k v l =>
    simp only [TxnOp.Under] at hu
    simp only [applyTxnOp]
    rw [underPfx_putKv pfx r k v l s hs hu]
  | putKeep k v =>
    simp only [TxnOp.Under] at hu
    simp only [applyTxnOp]
    rw [underPfx_putKv pfx r k v _ s hs hu, find_underPfx pfx k s hu]
  | putIgnVal k l =>
    simp only [TxnOp.Under] at hu
    simp only [applyTxnOp]
    rw [underPfx_putKv pfx r k _ _ s hs hu, find_underPfx pfx k s hu]

/-- A delete of a range under the prefix: the model's run on the restriction is the restriction
of its run. -/
theorem applyTxnOp_delete_underPfx (pfx : GoString) (r : w64) (s : List EtcdKv) (o : OpFull)
    (hu : KeyRangeUnder pfx o.key o.base.rangeEnd) :
    applyTxnOp r (underPfx pfx s) (.delete o) =
      (underPfx pfx (applyTxnOp r s (.delete o)).1, (applyTxnOp r s (.delete o)).2) := by
  simp only [applyTxnOp, v3rpc.rangeIn_underPfx pfx s o hu]
  unfold underPfx
  rw [filter_comm']

/-! ## The apply thread's log after a put or a delete -/

section applied
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A put's log** (`put_appended` with the change): the put's change at the log's next
revision. -/
theorem put_applied_exact (o : OpFull) (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : Log)
    (skip : Bool)
    (h : apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
      (.dispatched (.applied l false) skip)) :
    x'.log = x.log ++ [[putChangeOf o (findKey o.key (stateAfter x.log))]] := by
  have hk : apply.dispatchKind (apply.withHeader (irrPut o) hm) = .put := by
    simp [apply.dispatchKind, apply.withHeader, irrPut, apply.irrEmpty]
  obtain ⟨-, hd, hl, -⟩ := h
  rw [hl]
  unfold apply.dispatchStep at hd
  rw [hk] at hd
  simp only [apply.preV3Kind, apply.storeKind, Bool.false_eq_true, ↓reduceIte,
    false_or] at hd
  have hb := v3rpc.chainStep_applied_false x.chain hd
  unfold apply.backendStep at hb
  rw [hk] at hb
  obtain ⟨op, hop, hb | hb | hb⟩ := hb
  · cases hb.2
  · cases hb.2.2
  · simp [apply.withHeader, irrPut, apply.irrEmpty] at hop
    subst hop
    cases hb.2
    rfl

/-- **A delete's log**: the delete `op'` of the decoded request committed (nothing if its range
was empty). -/
theorem delete_applied_exact (op op' : OpFull) (hm : apply.HeaderModel) (rq' : apply.IRRModel)
    (x x' : apply.ApplyKV) (l : Log) (skip : Bool)
    (hw : irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq')
    (hop : rq'.deleteRange = some op')
    (h : apply.applyStep rq' true x x' (.dispatched (.applied l false) skip)) :
    x'.log = commitLog x.log (delChanges (stateAfter x.log) op') := by
  have hk : apply.dispatchKind rq' = .deleteRange := by
    rw [hw.2.2.1]
    simp [apply.dispatchKind, apply.withHeader, irrDeleteRange, apply.irrEmpty]
  obtain ⟨-, hd, hl, -⟩ := h
  rw [hl]
  unfold apply.dispatchStep at hd
  rw [hk] at hd
  simp only [apply.preV3Kind, apply.storeKind, Bool.false_eq_true, ↓reduceIte,
    false_or] at hd
  have hb := v3rpc.chainStep_applied_false x.chain hd
  unfold apply.backendStep at hb
  rw [hk] at hb
  obtain ⟨op'', hop', hb⟩ := hb
  rw [hop] at hop'
  cases hop'
  cases hb
  rfl

end applied

/-! ## The put -/

theorem putTxnOp_putLike (o : OpFull) :
    (putTxnOp o).isGet = false ∧ (∀ o', putTxnOp o ≠ .delete o') ∧
      (∀ cs ts es, putTxnOp o ≠ .txn cs ts es) ∧ (∀ s r, (applyTxnOp r s (putTxnOp o)).2 = .put) := by
  unfold putTxnOp
  repeat' split
  all_goals exact ⟨rfl, fun _ h => TxnOp.noConfusion h, fun _ _ _ h => TxnOp.noConfusion h,
    fun _ _ => rfl⟩

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **What a put's reply gives the clients' model** (`putReplied` with its update's floor: the
state the put linearized at, the state of the log it met, is at least a certified log `lf` longer
than `lo`; unit W-M3): `putResult`, its revision the log's next, with its token. -/
theorem putResult_of_reply (E : apply.AEnv GF) (γw : ReadNames) (F : Log) (lo : w64)
    (pfx : GoString) (o : OpFull) (cid mid : w64) (m : PutRespM) (hu : (putTxnOp o).Under pfx)
    (lf : Log) (hlo : sint.Z lo < lf.length) :
    storeSmall E.γ ∗ putReplied E γw F o (fun σ => iprop(⌜lf.length ≤ σ.rev + 1⌝)) cid mid m ⊢
      putResult (EM := v3rpc.etcdModelOfServer E) pfx lo (putTxnOp o) GoInterface.nil := by
  iintro ⟨#Hsm, Hrep⟩
  iunfold putReplied at Hrep
  icases Hrep with ⟨%hm, %x, %x', %l, %skip, %Hp, #Hcert, HMint, -, #Hcok, %Hfl⟩
  obtain ⟨Hst, -, -, -, -, -, H2, H4⟩ := Hp
  have hlog := put_applied_exact o hm x x' l skip Hst
  have hFl : lf.length ≤ x.log.length := by simp only [kvStateOf_rev, kvStateOf_kvs] at Hfl; omega
  obtain ⟨hg, hd, ht, hres⟩ := putTxnOp_putLike o
  iunfold revMinted at HMint
  icases HMint with (%He | ⟨%cs, %He, Htok⟩)
  · rw [hlog] at He
    exact absurd (congrArg List.length He) (by simp)
  have hr : sint.Z (W64 (x.log.length : Int)) = x.log.length := by word
  have hr1 : sint.Z (W64 (x.log.length : Int) - W64 1) = (x.log.length : Int) - 1 := by word
  have hS := stateAfter_sorted x.log
  have hrun : runTxn (W64 (x.log.length : Int)) (underPfx pfx (stateAfter x.log))
      (putTxn (putTxnOp o)) =
      (true, underPfx pfx (applyTxnOp (W64 (x.log.length : Int)) (stateAfter x.log) (putTxnOp o)).1,
        [.put]) := by
    have := applyTxnOp_put_underPfx pfx (W64 (x.log.length : Int)) (stateAfter x.log) hS
      (putTxnOp o) hg hd ht hu
    simp only [runTxn, putTxn, TxnModel.branch, List.all_nil, ↓reduceIte, runOps, this, hres]
  ihave #Hst1 := v3rpc.etcdState_of_cert E x'.log (W64 (x.log.length : Int) - W64 1) pfx
    (by rw [hr1]; omega) (by rw [hr1, hlog]; simp; omega) $$ [$Hsm $Hcert]
  ihave #Hst2 := v3rpc.etcdState_of_cert E x'.log (W64 (x.log.length : Int)) pfx
    (by rw [hr]; omega) (by rw [hr, hlog]; simp; omega) $$ [$Hsm $Hcert]
  icases Hst1 with ⟨#Hs1, %Hwf1⟩
  icases Hst2 with ⟨#Hs2, -⟩
  have e1 : stateAt x'.log (sint.Z (W64 (x.log.length : Int) - W64 1)).toNat = stateAfter x.log := by
    rw [hr1, hlog, show ((x.log.length : Int) - 1).toNat = x.log.length - 1 by omega,
      stateAt_append_lt _ _ (by omega), stateAt_last]
  have e2 : stateAt x'.log (sint.Z (W64 (x.log.length : Int))).toNat =
      (applyTxnOp (W64 (x.log.length : Int)) (stateAfter x.log) (putTxnOp o)).1 := by
    rw [hr, hlog, show ((x.log.length : Int)).toNat = (x.log ++ [[putChangeOf o
      (findKey o.key (stateAfter x.log))]]).length - 1 by simp, stateAt_last, stateAfter_put]
  rw [e1] at Hwf1
  unfold putResult
  iright
  isplitr
  · ipureintro; rfl
  iexists (W64 (x.log.length : Int)), (underPfx pfx (stateAfter x.log))
  rw [hrun]
  isplitr
  · iapply v3rpc.etcdReached_of_certOk E x'.log _ (by rw [hr, hlog]; simp; omega) $$ Hcok
  isplitr
  · ipureintro
    refine ⟨by rw [hr]; omega, by rw [hr]; omega, by rw [hr]; omega, Hwf1⟩
  isplitr
  · unfold txnStates
    simp only [txnWrote, List.any_cons, List.any_nil, TxnOpResult.wrote, Bool.or_false,
      ↓reduceIte]
    isplitl
    · rw [← e1]; iexact Hs1
    · rw [← e2]; iexact Hs2
  · rw [v3rpc.etcdModelOfServer_etcdRevToken]
    iexact Htok

/-- The put's operation, as the server decodes it: `txnOpOf`'s put of an `Op` that is a put is
the server's `putTxnOp` of its wire model. -/
theorem putTxnOp_wire (o : OpFull) (op : TxnOp) (h : txnOpOf o = some op) (ht : o.t = W64 2) :
    putTxnOp (putWireOf o) = op := by
  have hl := leafWire_txnOpOf o op h
  have h1 : o.t ≠ W64 1 := by rw [ht]; decide
  unfold leafWire at hl
  rw [if_neg h1, if_pos ht] at hl
  rw [hl]
  cases op with
  | get o' =>
    unfold txnOpOf at h
    rw [if_neg h1, if_pos ht] at h
    repeat' split at h
    all_goals simp at h
  | delete o' =>
    unfold txnOpOf at h
    rw [if_neg h1, if_pos ht] at h
    repeat' split at h
    all_goals simp at h
  | txn cs ts es =>
    unfold txnOpOf at h
    rw [if_neg h1, if_pos ht] at h
    repeat' split at h
    all_goals simp at h
  | _ => simp [opWire]

/-- **A put with a lease, in the clients' model** (a premise, persistent; 2026-10-15, unit T2: leases
are outside the KV model until unit T3, so no server spec covers a put with a lease): the triple
of `kv_put_result` for such a put. -/
def kvLeasedPutTodo (api : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(□ ∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key val : GoString)
      (sl : GoSlice) (gs : List (OpFull → OpFull)) (op : TxnOp) (lo : w64) (pfx : GoString),
    ⌜¬ (opPutModel key val gs).putPanics ∧ txnOpOf (opPutModel key val gs) = some op ∧
      op.Under pfx ∧ (opPutModel key val gs).t = W64 2 ∧
      (putWireOf (opPutModel key val gs)).leaseID ≠ W64 0⌝ -∗
    {{ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
        etcdReached (EM := v3rpc.etcdModelOfServer E) lo }}
      (App (App (App (App (Val #(methods (kvIfaceOf api).ty go!"Put" (kvIfaceOf api).v))
        (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        putResult (EM := v3rpc.etcdModelOfServer E) pfx lo op err }})

instance kvLeasedPutTodo_persistent (api : Loc) (E : apply.AEnv GF) :
    Persistent (kvLeasedPutTodo api E) := by
  unfold kvLeasedPutTodo; infer_instance

/-- **`kv.Put` on a `*kv` over a connection to etcd's server, in the clients' model** (at a
quiet or model context with `ctxErrClient`): `putResult`. 2026-10-15 (unit T2): a put with no
lease with the caller's update `kvAnyAu` (etcd's `Put` spec over the whole state), one with a
lease by the premise `kvLeasedPutTodo`. -/
theorem kv_put_result (api : Loc) (addr : List GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (op : TxnOp) (lo : w64)
    (pfx : GoString)
    (h : ¬ (opPutModel key val gs).putPanics ∧ txnOpOf (opPutModel key val gs) = some op ∧
      op.Under pfx ∧ (opPutModel key val gs).t = W64 2 ∧ opSizeOk (opPutModel key val gs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isServerRead s E γr ∗
        kvObjAt api addr ∗ kvRegs (srvsAt addr E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
        etcdReached (EM := v3rpc.etcdModelOfServer E) lo ∗ kvAnyAu E γr ∗ kvLeasedPutTodo api E }}
      (App (App (App (App (Val #(methods (kvIfaceOf api).ty go!"Put" (kvIfaceOf api).v))
        (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        putResult (EM := v3rpc.etcdModelOfServer E) pfx lo op err }} := by
  obtain ⟨hpan, hop, hu, ht, hsz⟩ := h
  have hw := putTxnOp_wire _ _ hop ht
  iintro %Φ ⟨#Pc, #Hsrd, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #Hlo, #Hany, #Hlp⟩ HΦ
  by_cases hl : (putWireOf (opPutModel key val gs)).leaseID = W64 0
  rotate_left
  · iunfold kvLeasedPutTodo at Hlp
    ihave #Ht := Hlp $$ %ci %cd %key %val %sl %gs %op %lo %pfx %(⟨hpan, hop, hu, ht, hl⟩)
    iapply Ht $$ [] HΦ
    iframe #
  ihave ⟨%lf, #Hcl, %Hll⟩ := certOk_of_reached E lo $$ Hlo
  ihave ⟨%F, #HF, %HF2⟩ := floor0_of_read s E γr $$ Hsrd
  ihave #Hsm := storeSmall_of_read s E γr $$ Hsrd
  iunfold kvAnyAu at Hany
  imod Hany $$ %(KVOp.put (putWireOf (opPutModel key val gs))) %lf Hcl with #Hau
  -- (2026-10-19, D21 M6) a persistent update, its result persistent
  ihave #Hau1 : □ kvOpAu1 γr.kv (.put (putWireOf (opPutModel key val gs)))
      (fun σ => iprop(□ ⌜lf.length ≤ σ.rev + 1⌝)) $$ []
  · imodintro; iapply kvOpAu_one $$ Hau
  ihave #Hus := putUpd_srvsAt addr E γr cid mid _ _ $$ Hau1
  iapply (v3.kv.wp_PutM api (srvsAt addr E γr cid mid) ci cd key val sl gs
    (fun σ => iprop(□ ⌜lf.length ≤ σ.rev + 1⌝)) F) $$ []
  · iframe #
    isplitl []
    · iapply isKV_srvsAt $$ [Hkv Hrpc]; iframe #
    isplitl []
    · ipureintro; exact ⟨hpan, ht, hl⟩
    isplitl []
    · iapply floorsAt_srvsAt $$ HF
    isplitl []; rotate_left
    · ipureintro; exact hsz
    iapply kvReqPre_box
    imodintro
    inext
    iexact Hus
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold putCallOut at Hout
  icases Hout with (⟨%Herr, %m, -, Hq⟩ | ⟨%Herr, -⟩)
  · subst Herr
    ihave Hq := putAns_srvsAt addr E γr cid mid F _ _ m $$ Hq
    ihave Hq := putReplied_mono E γr F _ (fun σ => iprop(□ ⌜lf.length ≤ σ.rev + 1⌝))
      (fun σ => iprop(⌜lf.length ≤ σ.rev + 1⌝)) cid mid m (fun _ => intuitionistically_elim) $$ Hq
    rw [← hw] at hu ⊢
    iapply putResult_of_reply E γr F lo pfx _ cid mid m hu lf Hll $$ [$Hsm $Hq]
  · unfold putResult
    ileft
    ipureintro; exact Herr.1

/-- **A real `*kv` meets the recipes' put contract** (`isEtcdPutKVTodo`) at the server's model:
`kv.Put(context.TODO(), ...)` returns `putResult` (see the file header). Premises: the
registration of etcd's `Put` at `addr`, the server's read side (`isServerRead`: the first
certificate and `storeSmall`), and that `errors.As` can take `*rpctypes.EtcdError` (`hAs`). -/
theorem isEtcdPutKVTodo_of_kv (api : Loc) (addr : List GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (pfx : GoString)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isServerRead s E γr ∗
        kvObjAt api addr ∗ kvRegs (srvsAt addr E γr cid mid) ∗
        kvAnyAu E γr ∗ kvLeasedPutTodo api E ⊢
      isEtcdPutKVTodo (EM := v3rpc.etcdModelOfServer E) (kvIfaceOf api) pfx := by
  iintro ⟨#Pc, #Hsrd, #Hkv, #Hrpc, #Hany, #Hlp⟩
  unfold isEtcdPutKVTodo
  iintro !> %key %val %sl %gs %op %lo %Φ !> ⟨#Hopts, #Hlo, %Hp⟩ HΦ
  imod (todo_ctx (GF := GF) hAs) with ⟨%cd, #Hctx, #Hce⟩
  iapply (kv_put_result api addr s E γr cid mid todoCtxVal cd key val sl gs op lo pfx Hp) $$ []
  · iframe #
  iexact HΦ

/-! ## The delete -/

/-- **What a delete's reply gives the clients' model** (`deleteReplied` with its update's floor,
as `putResult_of_reply`, unit W-M3; for a delete of a range under `pfx` whose end is not `[0]`):
`deleteResult`, its revision the log's next if it deleted a key, the last otherwise. -/
theorem deleteResult_of_reply (E : apply.AEnv GF) (γw : ReadNames) (F : Log) (lo : w64)
    (pfx : GoString) (o : OpFull) (cid mid : w64) (m : DelRespM)
    (hu : KeyRangeUnder pfx o.key o.base.rangeEnd) (hz : o.base.rangeEnd ≠ [W8 0])
    (lf : Log) (hlo : sint.Z lo < lf.length) :
    storeSmall E.γ ∗
        deleteReplied E γw F (deleteWireOf o) (fun σ => iprop(⌜lf.length ≤ σ.rev + 1⌝)) cid mid m ⊢
      deleteResult (EM := v3rpc.etcdModelOfServer E) pfx lo o GoInterface.nil := by
  iintro ⟨#Hsm, Hrep⟩
  iunfold deleteReplied at Hrep
  icases Hrep with ⟨%hm, %rq', %op', %x, %x', %l, %skip, %Hp, #Hcert, -, -, #Hcok, %Hfl⟩
  obtain ⟨Hw, Hop, Hz, Hst, -, -, -, -, -, -, H2, H4⟩ := Hp
  have hnz : irrNoZeroEnd (irrDeleteRange (deleteWireOf o)) := by
    refine ⟨fun o' h => by simp [irrDeleteRange, apply.irrEmpty] at h, fun o' h => ?_,
      fun t h => by simp [irrDeleteRange, apply.irrEmpty] at h⟩
    simp only [irrDeleteRange, Option.some.injEq] at h
    subst h
    simpa [deleteWireOf, txn.deleteOpOf] using hz
  have hop' : op' = deleteWireOf o := Hz hnz
  subst hop'
  have hlog := delete_applied_exact _ _ hm rq' x x' l skip Hw Hop Hst
  have hFl : lf.length ≤ x.log.length := by simp only [kvStateOf_rev, kvStateOf_kvs] at Hfl; omega
  have hrin : rangeIn (stateAfter x.log) (deleteWireOf o) = rangeIn (stateAfter x.log) o := rfl
  have happ : ∀ r st, applyTxnOp r st (.delete (deleteWireOf o)) = applyTxnOp r st (.delete o) :=
    fun _ _ => rfl
  have hS := stateAfter_sorted x.log
  have hrun : ∀ r, runTxn r (underPfx pfx (stateAfter x.log)) (deleteTxn o) =
      (true, underPfx pfx (applyTxnOp r (stateAfter x.log) (.delete o)).1,
        [.delete (rangeIn (stateAfter x.log) o).length]) := by
    intro r
    have := applyTxnOp_delete_underPfx pfx r (stateAfter x.log) o hu
    simp only [runTxn, deleteTxn, TxnModel.branch, List.all_nil, ↓reduceIte, runOps, this]
    simp [applyTxnOp]
  ihave %Hcl := v3rpc.idxCert_pure E.γ.idx x'.log $$ Hcert
  unfold deleteResult
  iright
  isplitr
  · ipureintro; rfl
  by_cases hE : rangeIn (stateAfter x.log) o = []
  · -- nothing deleted: the log as it was, the revision its last
    have hdc : delChanges (stateAfter x.log) (deleteWireOf o) = [] := by
      simp [delChanges, hrin, hE]
    rw [hdc] at hlog
    simp only [commitLog, ↓reduceIte] at hlog
    rw [hlog]
    have hr : sint.Z (W64 ((x.log.length : Int) - 1)) = (x.log.length : Int) - 1 := by word
    ihave #Hst1 := v3rpc.etcdState_of_cert_last E x.log pfx H2 (by omega) $$ [$Hsm $Hcert]
    icases Hst1 with ⟨#Hs1, %Hwf1⟩
    iexists (W64 ((x.log.length : Int) - 1)), (underPfx pfx (stateAfter x.log))
    rw [hrun]
    isplitr
    · iapply v3rpc.etcdReached_of_certOk E x.log _ (by rw [hr]; omega) $$ Hcok
    isplitr
    · ipureintro
      refine ⟨by rw [hr]; omega, by rw [hr]; omega, by rw [hr]; omega, Hwf1⟩
    unfold txnStates
    simp only [txnWrote, List.any_cons, List.any_nil, TxnOpResult.wrote, Bool.or_false, hE,
      List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    iexact Hs1
  · -- a key deleted: the next revision
    have hdc : delChanges (stateAfter x.log) (deleteWireOf o) ≠ [] := by
      simp [delChanges, hrin, hE]
    have hlog' : x'.log = x.log ++ [delChanges (stateAfter x.log) (deleteWireOf o)] := by
      rw [hlog]; simp [commitLog, hdc]
    have hr : sint.Z (W64 (x.log.length : Int)) = x.log.length := by word
    have hr1 : sint.Z (W64 (x.log.length : Int) - W64 1) = (x.log.length : Int) - 1 := by word
    ihave #Hst1 := v3rpc.etcdState_of_cert E x'.log (W64 (x.log.length : Int) - W64 1) pfx
      (by rw [hr1]; omega) (by rw [hr1, hlog']; simp; omega) $$ [$Hsm $Hcert]
    ihave #Hst2 := v3rpc.etcdState_of_cert E x'.log (W64 (x.log.length : Int)) pfx
      (by rw [hr]; omega) (by rw [hr, hlog']; simp; omega) $$ [$Hsm $Hcert]
    icases Hst1 with ⟨#Hs1, %Hwf1⟩
    icases Hst2 with ⟨#Hs2, -⟩
    have e1 : stateAt x'.log (sint.Z (W64 (x.log.length : Int) - W64 1)).toNat =
        stateAfter x.log := by
      rw [hr1, hlog', show ((x.log.length : Int) - 1).toNat = x.log.length - 1 by omega,
        stateAt_append_lt _ _ (by omega), stateAt_last]
    have e2 : stateAt x'.log (sint.Z (W64 (x.log.length : Int))).toNat =
        (applyTxnOp (W64 (x.log.length : Int)) (stateAfter x.log) (.delete o)).1 := by
      rw [hr, show ((x.log.length : Int)).toNat = x'.log.length - 1 by rw [hlog']; simp,
        stateAt_last, hlog, stateAfter_commit_delete]
      rfl
    rw [e1] at Hwf1
    iexists (W64 (x.log.length : Int)), (underPfx pfx (stateAfter x.log))
    rw [hrun]
    isplitr
    · iapply v3rpc.etcdReached_of_certOk E x'.log _ (by rw [hr, hlog']; simp; omega) $$ Hcok
    isplitr
    · ipureintro
      refine ⟨by rw [hr]; omega, by rw [hr]; omega, by rw [hr]; omega, Hwf1⟩
    have hne : ((rangeIn (stateAfter x.log) o).length != 0) = true := by
      simp [List.length_eq_zero_iff, hE]
    unfold txnStates
    simp only [txnWrote, List.any_cons, List.any_nil, TxnOpResult.wrote, Bool.or_false, hne,
      ↓reduceIte]
    isplitl
    · rw [← e1]; iexact Hs1
    · rw [← e2]; iexact Hs2

/-- **`kv.Delete` on a `*kv` over a connection to etcd's server, in the clients' model** (at a
quiet or model context with `ctxErrClient`): `deleteResult`. -/
theorem kv_delete_result (api : Loc) (addr : List GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (lo : w64) (pfx : GoString)
    (h : ¬ opDeletePanics key gs ∧
      KeyRangeUnder pfx (opDeleteModel key gs).key (opDeleteModel key gs).base.rangeEnd ∧
      (opDeleteModel key gs).base.rangeEnd ≠ [W8 0] ∧ (opDeleteModel key gs).t = W64 3 ∧
      opSizeOk (opDeleteModel key gs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isServerRead s E γr ∗
        kvObjAt api addr ∗ kvRegs (srvsAt addr E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
        etcdReached (EM := v3rpc.etcdModelOfServer E) lo ∗ kvAnyAu E γr }}
      (App (App (App (Val #(methods (kvIfaceOf api).ty go!"Delete" (kvIfaceOf api).v))
        (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        deleteResult (EM := v3rpc.etcdModelOfServer E) pfx lo (opDeleteModel key gs) err }} := by
  obtain ⟨hpan, hu, hz, ht, hsz⟩ := h
  iintro %Φ ⟨#Pc, #Hsrd, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #Hlo, #Hnp⟩ HΦ
  ihave ⟨%lf, #Hcl, %Hll⟩ := certOk_of_reached E lo $$ Hlo
  ihave ⟨%F, #HF, %HF2⟩ := floor0_of_read s E γr $$ Hsrd
  ihave #Hsm := storeSmall_of_read s E γr $$ Hsrd
  iunfold kvAnyAu at Hnp
  imod Hnp $$ %(KVOp.deleteRange (deleteWireOf (opDeleteModel key gs))) %lf Hcl with #Hau
  -- (2026-10-20, linkv-txn stage A) a persistent update, its result persistent
  ihave #Hau1 : □ kvOpAu1 γr.kv (.deleteRange (deleteWireOf (opDeleteModel key gs)))
      (fun σ => iprop(□ ⌜lf.length ≤ σ.rev + 1⌝)) $$ []
  · imodintro; iapply kvOpAu_one $$ Hau
  ihave #Hus := delUpd_srvsAt addr E γr cid mid _ _ $$ Hau1
  iapply (v3.kv.wp_DeleteM api (srvsAt addr E γr cid mid) ci cd key sl gs
    (fun σ => iprop(□ ⌜lf.length ≤ σ.rev + 1⌝)) F) $$ []
  · iframe #
    isplitl []
    · iapply isKV_srvsAt $$ [Hkv Hrpc]; iframe #
    isplitl []
    · ipureintro; exact ⟨hpan, ht, by simpa [deleteWireOf, txn.deleteOpOf] using hz⟩
    isplitl []
    · iapply floorsAt_srvsAt $$ HF
    isplitl []; rotate_left
    · ipureintro; exact hsz
    iapply kvReqPre_box
    imodintro
    inext
    iexact Hus
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold deleteCallOut at Hout
  icases Hout with (⟨%Herr, %m, -, Hq⟩ | ⟨%Herr, -⟩)
  · subst Herr
    ihave Hq := delAns_srvsAt addr E γr cid mid F _ _ m $$ Hq
    ihave Hq := deleteReplied_mono E γr F _ (fun σ => iprop(□ ⌜lf.length ≤ σ.rev + 1⌝))
      (fun σ => iprop(⌜lf.length ≤ σ.rev + 1⌝)) cid mid m (fun _ => intuitionistically_elim) $$ Hq
    iapply deleteResult_of_reply E γr F lo pfx _ cid mid m hu hz lf Hll $$ [$Hsm $Hq]
  · unfold deleteResult
    ileft
    ipureintro; exact Herr.1

/-- **A real `*kv` meets the recipes' delete contract** (`isEtcdDeleteKVTodo`) at the server's
model: `kv.Delete(context.TODO(), ...)` returns `deleteResult` (see the file header). -/
theorem isEtcdDeleteKVTodo_of_kv (api : Loc) (addr : List GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (pfx : GoString)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isServerRead s E γr ∗
        kvObjAt api addr ∗ kvRegs (srvsAt addr E γr cid mid) ∗
        kvAnyAu E γr ⊢
      isEtcdDeleteKVTodo (EM := v3rpc.etcdModelOfServer E) (kvIfaceOf api) pfx := by
  iintro ⟨#Pc, #Hsrd, #Hkv, #Hrpc, #Hnp⟩
  unfold isEtcdDeleteKVTodo
  iintro !> %key %sl %gs %lo %Φ !> ⟨#Hopts, #Hlo, %Hp⟩ HΦ
  imod (todo_ctx (GF := GF) hAs) with ⟨%cd, #Hctx, #Hce⟩
  iapply (kv_delete_result api addr s E γr cid mid todoCtxVal cd key sl gs lo pfx Hp) $$ []
  · iframe #
  iexact HΦ

end proofs

end client
end EtcdGrove
end Perennial
