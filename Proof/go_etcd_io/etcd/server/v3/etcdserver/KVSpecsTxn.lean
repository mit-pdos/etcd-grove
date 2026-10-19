/-
**The top-level `Txn` spec of etcd's server, over the state machine** (2026-10-19; `notes/decisions.md`,
"The KV specs over a state machine (D22)"; as `KVSpecs.lean`'s, whose vocabulary it uses).
Lean-first (no Rocq counterpart).

* **The transactions it covers** (`TxnCovered`, stated over the state machine's request): every
  range at the transaction's revision, with a sort target and order of the protobuf's and not
  cut early (`issues/etcd-range-sort-none-limit.md`); every put with no lease and not keeping
  the key's lease; no range end `"\x00"` (the wire's encoding); none that makes the server panic
  (`EtcdSM.txnPanics`, `issues/etcd-txn-delete-then-ignore-put.md`), at any map; and not a
  serializable read-only one (it reads the member's store, as a serializable `Range`).
* **The two paths**: a read-only transaction goes through the read index (as `Range`; its
  update is the state machine's identity, `txnNext_readonly`), a writing one through raft (as
  `Put`).
* **The response** (`kvTxnResponseIs`): the header's revision and `Succeeded` the state machine's,
  each operation's response the server's response predicate (`txn.responseOpIs`) of the state
  machine's results (`resultsOf`): a range's key-values and count, a delete's count, a nested
  transaction's verdict and responses. A put's previous key-value, a delete's previous
  key-values and a range's `More` are left open, as the server's proof leaves them; a writing
  transaction's ranges may be answered header-only (`skip`: the proof does not yet exclude the
  apply's `SkipRangeExecution` for the proposer's own request).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVSpecs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

/-! ## The transactions the spec covers -/

/-- A range of a transaction is **cut early** (`issues/etcd-range-sort-none-limit.md`): sorted,
and the store reads with a limit. -/
def EtcdSM.RangeRequest.cutEarly (req : EtcdSM.RangeRequest) : Prop :=
  (EtcdSM.effectiveSortOrder req = EtcdSM.sortAscend ∨
    EtcdSM.effectiveSortOrder req = EtcdSM.sortDescend) ∧ 0 < sint.Z (EtcdSM.readLimit req)

mutual
/-- **An operation the spec covers**: a range at the transaction's revision (`revision = 0`),
with a sort target and order of the protobuf's, not cut early, and a range end other than
`"\x00"`; a put with no lease that does not keep the key's lease; a delete whose range end is not
`"\x00"`; a nested transaction whose comparisons' range ends are not `"\x00"` and whose
operations are covered. -/
def opCovered : EtcdSM.RequestOp → Prop
  | .range req => req.revision = W64 0 ∧ 0 ≤ sint.Z req.sortTarget ∧ sint.Z req.sortTarget ≤ 4 ∧
      (req.sortOrder = EtcdSM.sortNone ∨ req.sortOrder = EtcdSM.sortAscend ∨
        req.sortOrder = EtcdSM.sortDescend) ∧ ¬ req.cutEarly ∧ req.rangeEnd ≠ [W8 0]
  | .put req => req.lease = W64 0 ∧ req.ignoreLease = false
  | .deleteRange req => req.rangeEnd ≠ [W8 0]
  | .txn cs ts es => (∀ c ∈ cs, c.rangeEnd ≠ [W8 0]) ∧ opsCovered ts ∧ opsCovered es

/-- Every operation covered. -/
def opsCovered : List EtcdSM.RequestOp → Prop
  | [] => True
  | op :: ops => opCovered op ∧ opsCovered ops
end

/-- An operation is a range (and, for `ser`, a serializable one). -/
def EtcdSM.RequestOp.isRange (ser : Bool) : EtcdSM.RequestOp → Bool
  | .range req => if ser then req.serializable else true
  | _ => false

/-- **A transaction the spec covers** (see the file header). -/
def TxnCovered (req : EtcdSM.TxnRequest) : Prop :=
  (∀ c ∈ req.compare, c.rangeEnd ≠ [W8 0]) ∧ opsCovered req.success ∧ opsCovered req.failure ∧
  (∀ (s0 : EtcdSM.KVMap) (r : w64), EtcdSM.opsPanic s0 r s0
    (if req.compare.all (·.holds s0) then req.success else req.failure) = false) ∧
  ¬ ((req.success ++ req.failure).all (·.isRange true) = true)

/-! ## The server's premises from `TxnCovered` -/

/-- The server's effective sort order is the state machine's, or none (a range with no sort
set). -/
theorem effSortOrder_cases (o : OpFull) :
    o.effSortOrder = W64 0 ∨ o.effSortOrder = EtcdSM.effectiveSortOrder (rangeReqOf o) := by
  unfold OpFull.effSortOrder EtcdSM.effectiveSortOrder rangeReqOf
  dsimp only
  cases o.base.sortSet
  · left; rfl
  · right; rfl

theorem not_cutEarly (o : OpFull) (h : ¬ (rangeReqOf o).cutEarly) : ¬ txn.cutEarly o := by
  rintro ⟨he, hl⟩
  apply h
  rcases effSortOrder_cases o with h0 | h0
  · rw [h0] at he; rcases he with he | he <;> exact absurd he (by decide)
  · rw [h0] at he
    exact ⟨he, by rw [readLimit_eq]; exact hl⟩

mutual
theorem opPlain_of (op : TxnOp) : opCovered (requestOpOf op) → txn.opPlain op ∧ txnOpNoZeroEnd op := by
  match op with
  | .get o => intro h; exact ⟨h.1, h.2.2.2.2.2⟩
  | .put k v l => intro h; exact ⟨h.1, trivial⟩
  | .putKeep k v => intro h; exact absurd h.2 (by simp [txnPutReq])
  | .putIgnVal k l =>
    intro h
    refine ⟨?_, trivial⟩
    cases l with
    | none => exact absurd h.2 (by simp [txnPutReq])
    | some x => simp only [requestOpOf, opCovered, txnPutReq, Option.getD_some] at h; simp [txn.opPlain, h.1]
  | .delete o => intro h; exact ⟨trivial, h⟩
  | .txn cs ts es =>
    intro h
    obtain ⟨hc, hts, hes⟩ := h
    have h1 := opsPlain_of ts hts
    have h2 := opsPlain_of es hes
    refine ⟨⟨h1.1, h2.1⟩, ?_, h1.2, h2.2⟩
    intro c hcm
    exact hc (compareOf c) (List.mem_map.2 ⟨c, hcm, rfl⟩)

theorem opsPlain_of (ops : List TxnOp) :
    opsCovered (requestOpsOf ops) → txn.opsPlain ops ∧ txnOpsNoZeroEnd ops := by
  match ops with
  | [] => intro _; exact ⟨trivial, trivial⟩
  | op :: ops =>
    intro h
    obtain ⟨h1, h2⟩ := h
    have a := opPlain_of op h1
    have b := opsPlain_of ops h2
    exact ⟨⟨a.1, b.1⟩, a.2, b.2⟩
end

mutual
theorem opIG_of (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (op : TxnOp) :
    opCovered (requestOpOf op) → EtcdSM.opPanics s0 r s (requestOpOf op) = false →
      txn.OpIG true s0 r s op := by
  match op with
  | .get o =>
    intro h _
    exact ⟨h.1, ⟨h.2.1, h.2.2.1⟩, not_cutEarly o h.2.2.2.2.1⟩
  | .put k v l => intro _ _; trivial
  | .putKeep k v => intro h _; exact absurd h.2 (by simp [txnPutReq])
  | .putIgnVal k l =>
    intro _ hp
    simp only [txn.OpIG, txn.IgnOk]
    simp only [requestOpOf, txnPutReq, EtcdSM.opPanics, Bool.true_or, Bool.true_and,
      Bool.and_eq_false_iff, EtcdSM.KVMap.get_eq] at hp
    rcases hp with hp | hp
    · left; simpa using hp
    · right; exact ⟨trivial, by simpa using hp⟩
  | .delete o => intro _ _; trivial
  | .txn cs ts es =>
    intro h hp
    obtain ⟨-, hts, hes⟩ := h
    simp only [requestOpOf, EtcdSM.opPanics, all_holds_eq] at hp
    simp only [txn.OpIG]
    cases hc : cs.all (cmpHolds s0)
    · rw [hc] at hp; exact opsIG_of s0 r s es hes hp
    · rw [hc] at hp; exact opsIG_of s0 r s ts hts hp

theorem opsIG_of (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (ops : List TxnOp) :
    opsCovered (requestOpsOf ops) → EtcdSM.opsPanic s0 r s (requestOpsOf ops) = false →
      txn.OpsIG true s0 r s ops := by
  match ops with
  | [] => intro _ _; trivial
  | op :: ops =>
    intro h hp
    obtain ⟨h1, h2⟩ := h
    simp only [requestOpsOf, EtcdSM.opsPanic, Bool.or_eq_false_iff] at hp
    refine ⟨opIG_of s0 r s op h1 hp.1, ?_⟩
    have := hp.2
    rw [(runOp_eq s0 r s op).1] at this
    exact opsIG_of s0 r _ ops h2 this
end

/-- The branch of the state machine's request is the server's. -/
theorem txnReqOf_branch (t : TxnModel) (s0 : List EtcdKv) :
    (if (txnReqOf t).compare.all (·.holds s0) then (txnReqOf t).success else (txnReqOf t).failure) =
      requestOpsOf (t.branch (txn.txnOk s0 t)) := by
  simp only [txnReqOf, all_holds_eq]
  unfold TxnModel.branch
  split <;> rfl

theorem mem_requestOpsOf_get (ops : List TxnOp) (o : OpFull) (h : TxnOp.get o ∈ ops) :
    EtcdSM.RequestOp.range (rangeReqOf o) ∈ requestOpsOf ops := by
  induction ops with
  | nil => cases h
  | cons op ops ih =>
    simp only [requestOpsOf, List.mem_cons] at h ⊢
    rcases h with h | h
    · subst h; left; rfl
    · right; exact ih h

theorem requestOpsOf_append (a b : List TxnOp) :
    requestOpsOf (a ++ b) = requestOpsOf a ++ requestOpsOf b := by
  induction a with
  | nil => rfl
  | cons op ops ih => simp only [List.cons_append, requestOpsOf, ih]

theorem all_isRange (ops : List TxnOp) :
    (requestOpsOf ops).all (·.isRange true) = ops.all txn.opIsSerGet := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    simp only [requestOpsOf, List.all_cons, ih]
    congr 1
    cases op <;> simp [requestOpOf, EtcdSM.RequestOp.isRange, txn.opIsSerGet, rangeReqOf]

theorem opsCovered_mem (ops : List EtcdSM.RequestOp) (h : opsCovered ops) :
    ∀ op ∈ ops, opCovered op := by
  induction ops with
  | nil => intro _ h; cases h
  | cons op ops ih =>
    intro op' hm
    rcases List.mem_cons.1 hm with hm | hm
    · subst hm; exact h.1
    · exact ih h.2 op' hm

/-- **The server's premises of a covered transaction.** -/
theorem txnCovered_model (t : TxnModel) (h : TxnCovered (txnReqOf t)) :
    (txn.txnPlain t ∧ txnNoZeroEnd t ∧ txn.txnShape t) ∧ txn.txnGetsOk t ∧
      txn.txnSerializable t = false := by
  obtain ⟨hc, hs, hf, hp, hser⟩ := h
  have a := opsPlain_of t.thenOps hs
  have b := opsPlain_of t.elseOps hf
  refine ⟨⟨⟨a.1, b.1⟩, ⟨fun c hcm => hc (compareOf c) (List.mem_map.2 ⟨c, hcm, rfl⟩), a.2, b.2⟩,
    ?_⟩, ?_, ?_⟩
  · intro s0 r _
    have hp' := hp s0 r
    rw [txnReqOf_branch] at hp'
    have hcov : opsCovered (requestOpsOf (t.branch (txn.txnOk s0 t))) := by
      unfold TxnModel.branch; split
      · exact hs
      · exact hf
    exact opsIG_of s0 r s0 _ hcov hp'
  · intro o ho
    have hm : EtcdSM.RequestOp.range (rangeReqOf o) ∈ (txnReqOf t).success ++ (txnReqOf t).failure := by
      rcases List.mem_append.1 ho with ho | ho
      · exact List.mem_append_left _ (mem_requestOpsOf_get _ o ho)
      · exact List.mem_append_right _ (mem_requestOpsOf_get _ o ho)
    have hcv : opCovered (.range (rangeReqOf o)) := by
      rcases List.mem_append.1 hm with hm | hm
      · exact opsCovered_mem _ hs _ hm
      · exact opsCovered_mem _ hf _ hm
    exact ⟨hcv.1, not_cutEarly o hcv.2.2.2.2.1, hcv.2.1, hcv.2.2.1⟩
  · cases hst : txn.txnSerializable t
    · rfl
    · exfalso
      apply hser
      have : (txnReqOf t).success ++ (txnReqOf t).failure =
          requestOpsOf (t.thenOps ++ t.elseOps) := (requestOpsOf_append _ _).symm
      rw [this, all_isRange]
      exact hst

/-! ## Read-only transactions, applied transactions -/

/-- The key check of gets passes. -/
theorem pathsIgnOk_gets (s0 : List EtcdKv) :
    ∀ ops : List TxnOp, (∀ op ∈ ops, txn.opIsGet op = true) → txn.PathsIgnOk s0 ops
  | [], _ => trivial
  | op :: ops, h => by
    have hop := h op List.mem_cons_self
    cases op with
    | get o => exact ⟨trivial, pathsIgnOk_gets s0 ops (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩
    | _ => simp [txn.opIsGet] at hop

/-- **A read-only transaction changes nothing.** -/
theorem txnNext_readonly (t : TxnModel) (h : txn.txnReadonly t = true) :
    EtcdSM.txnNext (txnReqOf t) = fun σ => σ := by
  rw [txnNext_eq]
  funext σ
  unfold kvOpStep KVState.commit txn.srvRunTxn
  simp [txn.srvOps_gets _ _ _ _ (txn.readonly_branch t h _)]

/-- A transaction applied with no error through any chain passed the backend's key check. -/
theorem chainStep_applied_false' : ∀ (c : apply.Chain) {rq : apply.IRRModel} {log l : mvcc.Log},
    apply.chainStep apply.backendStep c rq log (.applied l false) →
      apply.backendStep rq log (.applied l false)
  | .backend, _, _, _, h => h
  | .corrupt c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · cases h
    · exact chainStep_applied_false' c h
  | .capped c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · cases h
    · split at h
      · rcases h with h | h
        · cases h
        · exact chainStep_applied_false' c h
      · exact chainStep_applied_false' c h
  | .auth _ c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · rcases h with ⟨-, h⟩ | h
      · cases h
      · exact chainStep_applied_false' c h
    · exact chainStep_applied_false' c h
  | .quota c, _, _, _, h => by
    simp only [apply.chainStep] at h
    exact chainStep_applied_false' c h

/-- **An applied transaction passed its key check** at the log it met. -/
theorem txn_applied_check (t : TxnModel) (rq' : apply.IRRModel) (x x' : apply.ApplyKV)
    (l : mvcc.Log) (skip : Bool) (hk : apply.dispatchKind rq' = .txn) (ht : rq'.txn = some t)
    (h : apply.applyStep rq' true x x' (.dispatched (.applied l false) skip)) :
    txn.PathsIgnOk (mvcc.stateAfter x.log)
      (t.branch (txn.txnOk (mvcc.stateAfter x.log) t)) := by
  obtain ⟨-, hd, -, -⟩ := h
  unfold apply.dispatchStep at hd
  rw [hk] at hd
  simp only [apply.preV3Kind, apply.storeKind, Bool.false_eq_true, ↓reduceIte, false_or] at hd
  have hb := chainStep_applied_false' x.chain hd
  unfold apply.backendStep at hb
  rw [hk] at hb
  obtain ⟨t'', ht'', ⟨hb, -⟩ | ⟨-, -, hp⟩⟩ := hb
  · cases hb
  · rw [ht] at ht''
    cases ht''
    exact hp

/-! ## The spec -/

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `*pb.TxnRequest` `r` is the request `req`** (read-only), its puts' `prev_kv` flags
taken false (they change neither the state nor the answers the spec covers, and the server's
model does not keep them). -/
def kvTxnRequestIs (r : Loc) (req : EtcdSM.TxnRequest) : IProp GF :=
  iprop(∃ t : TxnModel, txn.txnRequestIs r t ∗ ⌜txnReqOf t = req⌝)

/-- **The `*pb.TxnResponse` `resp` is the response `res` to `req`** (see the file header): its
header's revision and `Succeeded`, each operation's response the server's response predicate of
the state machine's results, ranges answered header-only if `skip`; the header's other fields
owned. -/
def kvTxnResponseIs (resp : Loc) (req : EtcdSM.TxnRequest) (res : EtcdSM.TxnResult) : IProp GF :=
  iprop(∃ (t : TxnModel) (skip : Bool), ⌜txnReqOf t = req⌝ ∗
    txn.txnResponseIs skip resp (W64 (res.revision : Int)) t res.succeeded
      (resultsOf res.results) ∗
    txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp) ∗
    ⌜1 ≤ res.revision ∧ res.revision + 3 ≤ 2 ^ 63⌝)

end defs

section txn
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`s.Txn(ctx, r)`, over the state machine**: for a transaction the spec covers
(`TxnCovered`), from a context carrying no trace: success, the client's `□ Q σ` at the state `σ`
the transaction took effect on and the state machine's result there (`EtcdSM.txn`, which
succeeds), the response its (`kvTxnResponseIs`); or an error. -/
def EtcdServer.Txn.kvSpec : Prop :=
  ∀ (s : Loc) (γ : KVNames) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc)
    (req : EtcdSM.TxnRequest) (Q : EtcdSM.State → IProp GF),
  receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ownEtcdServer s γ ∗ context.isContext ctx cd ∗ traceutil.ctxTraceIs ctx none ∗
      kvTxnRequestIs r req ∗ ⌜TxnCovered req⌝ ∗ etcdAU γ (EtcdSM.txnNext req) Q }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Txn"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ownEtcdServer s γ ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (σ : EtcdSM.State) (res : EtcdSM.TxnResult),
          ⌜EtcdSM.txn req σ = .ok (EtcdSM.txnNext req σ, res)⌝ ∗ □ Q σ ∗
          kvTxnResponseIs resp req res) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

/-- The state machine's result at the state of a log `l` whose run's response the server gave. -/
theorem txn_result_at (t : TxnModel) (l : mvcc.Log) (hl : 2 ≤ l.length)
    (hp : txn.PathsIgnOk (mvcc.stateAfter l) (t.branch (txn.txnOk (mvcc.stateAfter l) t))) :
    ∃ res : EtcdSM.TxnResult,
      EtcdSM.txn (txnReqOf t) (kvStateOf l) = .ok (EtcdSM.txnNext (txnReqOf t) (kvStateOf l), res) ∧
      res.revision = mvcc.writeRev l
        (txn.srvRunTxn (W64 (l.length : Int)) (mvcc.stateAfter l) t).2.1 ∧
      res.succeeded = (txn.srvRunTxn (W64 (l.length : Int)) (mvcc.stateAfter l) t).1 ∧
      resultsOf res.results = (txn.srvRunTxn (W64 (l.length : Int)) (mvcc.stateAfter l) t).2.2 := by
  have hne : l ≠ [] := by intro h; rw [h] at hl; simp at hl
  have hsucc := kvStateOf_rev_succ l hne
  have hw : W64 (((kvStateOf l).rev + 1 : Nat) : Int) = W64 (l.length : Int) := by rw [hsucc]
  obtain ⟨res, h1, h2, h3, h4⟩ := txn_ok t (kvStateOf l) (kvStateOf_revs_ne_nil l hne)
    (by rw [kvStateOf_kvs]; exact hp)
  rw [kvStateOf_kvs, hw] at h2 h4
  rw [kvStateOf_kvs] at h3
  refine ⟨res, ?_, ?_, h3, h4⟩
  · rw [h1, txnNext_eq]
  · rw [h2]
    unfold mvcc.writeRev
    rw [kvStateOf_rev]
    split <;> omega

/-- **`EtcdServer.Txn.kvSpec`**, from the linked `EtcdServer.wp_Txn`. -/
theorem EtcdServer.wp_Txn_kv : EtcdServer.Txn.kvSpec (GF := GF) (hG := hG) := by
  intro s γ ctx cd r req Q hR
  iintro %Φ ⟨#Hpkg, Hown, #Hctx, #Htr, Hreq, %Hcov, #Hau⟩ HΦ
  iunfold ownEtcdServer at Hown
  icases Hown with ⟨%E, %ρ, %Hρ, #Hsrv, #Hrd, Hslot⟩
  iunfold srvCallSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrr, HRD⟩
  imod (mvcc.idxCert_nil (GF := GF) E.γ.idx) with #Hcert
  imod (monoNatLbOwn_0 (GF := GF) ρ.rd.committed) with #Hc0
  iunfold kvTxnRequestIs at Hreq
  icases Hreq with ⟨%t, #Hreq, %Ht⟩
  subst Ht
  obtain ⟨hperm, hgets, hser⟩ := txnCovered_model t Hcov
  iapply (EtcdServer.wp_Txn s E ρ ρ.rd (W64 0) ctx cd r t Q
    (fun L => iprop(□ Q (kvStateOf (kvModel ρ.rd.kv L)))) none true []) $$ [Hlt Hsr Hlg Hrr HRD]
  · iframe #
    iframe Hlt
    isplitr
    · iunfold idCred; ipureintro; exact hR
    isplitl
    · iunfold srvRdCall
      iframe Hsr Hlg Hrr HRD
      iunfold committedAtLeast
      rw [show uint.nat (W64 0) = 0 from rfl]
      iexact Hc0
    isplitr
    · iunfold traceutil.ownTraceOpt; itrivial
    isplitr
    · ipureintro; intro _; exact hgets
    cases hro : txn.txnReadonly t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iunfold txnPermit
      isplitr
      · ipureintro; exact hperm
      iunfold kvOpAu
      rw [← txnNext_eq, Hρ]
      iexact Hau
    · simp only [↓reduceIte]
      iunfold kvDep
      ileft
      iexists Q
      isplitr
      · ipureintro; rfl
      iunfold kvReadAu
      rw [show ρ.rd.kv = γ from Hρ, ← txnNext_readonly t hro]
      iexact Hau
  inext
  iintro %resp %err ⟨Hlt, Hcall, Hout⟩
  iunfold srvRdCall at Hcall
  icases Hcall with ⟨Hsr, Hlg, -, Hrr, HRD⟩
  iapply HΦ
  isplitl [Hlt HRD Hsr Hlg Hrr]
  · iunfold ownEtcdServer
    iexists E, ρ
    iframe #
    isplitr
    · ipureintro; exact Hρ
    iunfold srvCallSlot
    iframe
  cases hro : txn.txnReadonly t
  · -- a writing transaction, through raft
    simp only [hro, Bool.false_eq_true, ↓reduceIte]
    icases Hout with (⟨⟨%Herr, -⟩, Hok⟩ | ⟨⟨-, %Herr⟩, #Herr', -⟩)
    · ileft
      isplitr
      · ipureintro; exact Herr
      iunfold txnAppliedOk at Hok
      icases Hok with ⟨%hm, %rq', %t', %x, %x', %l, %skip, %Hp, Hans, Hhdr, -, -, -, -, #HQ⟩
      obtain ⟨hw, ht', hz, hstep, -⟩ := Hp
      have hnz : irrNoZeroEnd (irrTxn t) := by
        refine ⟨fun o' h => by simp [irrTxn, apply.irrEmpty] at h,
          fun o' h => by simp [irrTxn, apply.irrEmpty] at h, fun t'' h => ?_⟩
        simp only [irrTxn, Option.some.injEq] at h
        subst h
        exact hperm.2.1
      have htt := hz hnz
      subst t'
      have hk : apply.dispatchKind rq' = .txn := by
        rw [hw.2.2.1]
        simp [apply.dispatchKind, apply.withHeader, irrTxn, apply.irrEmpty]
      have hpi := txn_applied_check t rq' x x' l skip hk ht' hstep
      simp only [apply.txnOutcomeIs]
      icases Hans with ⟨#Hresp, -⟩
      iunfold apply.appliedHdr at Hhdr
      icases Hhdr with ⟨Hho, %Hb⟩
      obtain ⟨res, h1, h2, h3, h4⟩ := txn_result_at t x.log (by omega) hpi
      iexists kvStateOf x.log, res
      isplitr
      · ipureintro; exact h1
      iframe HQ
      iunfold kvTxnResponseIs
      iexists t, skip
      isplitr
      · ipureintro; rfl
      rw [h2, h3, h4]
      iframe Hresp Hho
      ipureintro
      unfold mvcc.writeRev
      split <;> omega
    · iright
      iframe Herr'
      ipureintro; exact Herr
  · -- a read-only transaction, through the read index
    simp only [hro, ↓reduceIte]
    icases Hout with ⟨-, (⟨⟨%Herr, -⟩, Hok⟩ | ⟨%Herr, #Herr'⟩)⟩
    · ileft
      isplitr
      · ipureintro; exact Herr
      iunfold txnReadOk at Hok
      simp only [hser, Bool.false_eq_true, ↓reduceIte]
      icases Hok with ⟨%l, -, -, %Hl, -, ⟨%L, -, %HL, #HQ⟩, #Hresp, Hho⟩
      obtain ⟨h2, h3', -⟩ := Hl
      have hpi : txn.PathsIgnOk (mvcc.stateAfter l)
          (t.branch (txn.txnOk (mvcc.stateAfter l) t)) :=
        pathsIgnOk_gets _ _ (txn.readonly_branch t hro _)
      obtain ⟨res, h1, hrv, h3, h4⟩ := txn_result_at t l h2 hpi
      have hnc : (txn.srvRunTxn (W64 (l.length : Int)) (mvcc.stateAfter l) t).2.1 = [] := by
        unfold txn.srvRunTxn
        exact txn.srvOps_gets _ _ _ _ (txn.readonly_branch t hro _)
      rw [hnc] at hrv
      iexists kvStateOf l, res
      isplitr
      · ipureintro; exact h1
      isplitr
      · rw [← HL]; iexact HQ
      iunfold kvTxnResponseIs
      iexists t, false
      isplitr
      · ipureintro; rfl
      have hrev : W64 ((res.revision : Nat) : Int) = W64 ((l.length : Int) - 1) := by
        rw [hrv]; unfold mvcc.writeRev; simp only [↓reduceIte]; congr 1; omega
      rw [hrev, h3, h4]
      iframe Hresp Hho
      ipureintro
      rw [hrv]; unfold mvcc.writeRev; simp only [↓reduceIte]; omega
    · iright
      iframe Herr'
      ipureintro; exact Herr

end txn

end EtcdGrove
end Perennial
