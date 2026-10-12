/-
Lemmas for the proofs of `executeTxn`, `txn` and `Txn` (txn unit 3): the server's run of a list
of operations split at an index, the requests' and responses' predicates element by element.
Lean-first; see `TxnRun.lean`, `InvTxn.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvTxn
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Changes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__Changes

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## The run, split -/

theorem applyChanges_nil' (r : w64) (s : List EtcdKv) : mvcc.applyChanges r s [] = s := rfl

/-- **The run of `a ++ b`**: `a`'s, then `b`'s at the state `a`'s changes left. -/
theorem srvOps_append (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (a b : List TxnOp),
      srvOps s0 r s (a ++ b) =
        ((srvOps s0 r s a).1 ++ (srvOps s0 r (mvcc.applyChanges r s (srvOps s0 r s a).1) b).1,
          (srvOps s0 r s a).2 ++ (srvOps s0 r (mvcc.applyChanges r s (srvOps s0 r s a).1) b).2)
  | s, [], b => by simp [srvOps_nil, applyChanges_nil']
  | s, x :: a, b => by
    rw [List.cons_append, srvOps_cons, srvOps_append s0 r _ a b, srvOps_cons]
    simp only [List.append_assoc, List.cons_append, applyChanges_append]

theorem srvOps_single (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (op : TxnOp) :
    srvOps s0 r s [op] = ((srvOp s0 r s op).1, [(srvOp s0 r s op).2]) := by
  rw [srvOps_cons, srvOps_nil]; simp

/-- The run of the first `i + 1` operations: the first `i`'s, then the `i`-th's. -/
theorem srvOps_take_succ (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (ops : List TxnOp)
    (i : Nat) (op : TxnOp) (h : ops[i]? = some op) :
    srvOps s0 r s (ops.take (i + 1)) =
      ((srvOps s0 r s (ops.take i)).1 ++
          (srvOp s0 r (mvcc.applyChanges r s (srvOps s0 r s (ops.take i)).1) op).1,
        (srvOps s0 r s (ops.take i)).2 ++
          [(srvOp s0 r (mvcc.applyChanges r s (srvOps s0 r s (ops.take i)).1) op).2]) := by
  have hl : ops.take (i + 1) = ops.take i ++ [op] := by rw [List.take_add_one, h]; rfl
  rw [hl, srvOps_append, srvOps_single]

/-- The run of all the operations: the first `i`'s, then the rest's. -/
theorem srvOps_take_drop (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (ops : List TxnOp)
    (i : Nat) :
    srvOps s0 r s ops =
      ((srvOps s0 r s (ops.take i)).1 ++
          (srvOps s0 r (mvcc.applyChanges r s (srvOps s0 r s (ops.take i)).1) (ops.drop i)).1,
        (srvOps s0 r s (ops.take i)).2 ++
          (srvOps s0 r (mvcc.applyChanges r s (srvOps s0 r s (ops.take i)).1) (ops.drop i)).2) := by
  conv => lhs; rw [← List.take_append_drop i ops]
  rw [srvOps_append]

theorem opsOk_append (w : Bool) (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (a b : List TxnOp),
      OpsOk w s0 r s (a ++ b) ↔
        OpsOk w s0 r s a ∧ OpsOk w s0 r (mvcc.applyChanges r s (srvOps s0 r s a).1) b
  | s, [], b => by simp [OpsOk, srvOps_nil, applyChanges_nil']
  | s, x :: a, b => by
    rw [List.cons_append]
    simp only [OpsOk]
    rw [opsOk_append w s0 r _ a b, srvOps_cons]
    simp only [applyChanges_append]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- The premises of the operations from the `i`-th on, at the state the first `i` left. -/
theorem opsOk_drop' (w : Bool) (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (ops : List TxnOp)
    (i : Nat) (h : OpsOk w s0 r s ops) :
    OpsOk w s0 r (mvcc.applyChanges r s (srvOps s0 r s (ops.take i)).1) (ops.drop i) := by
  rw [← List.take_append_drop i ops, opsOk_append] at h
  exact h.2

/-- The leases an operation of the list names are the list's. -/
theorem opsLeases_mem (s0 : List EtcdKv) :
    ∀ (ops : List TxnOp) (op : TxnOp), op ∈ ops → ∀ l ∈ opLeases s0 op, l ∈ opsLeases s0 ops
  | [], _, h, _, _ => by cases h
  | x :: ops, op, h, l, hl => by
    rw [opsLeases, List.mem_append]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl hl
    · exact Or.inr (opsLeases_mem s0 ops op h l hl)

/-- A get makes no change. -/
theorem srvOp_get (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (o : OpFull) :
    srvOp s0 r s (.get o) = ([], .range (rangeSel s o) (rangeIn s o).length) := by
  simp [srvOp]

/-- The pending state after more changes. -/
theorem pendState_append (ilog : mvcc.Log) (pend cs : List mvcc.Change) :
    pendState ilog (pend ++ cs) = mvcc.applyChanges (W64 (ilog.length : Int)) (pendState ilog pend) cs := by
  unfold pendState; rw [applyChanges_append]

theorem putTxnOp_ne_get (o o' : OpFull) : TxnOp.get o' ≠ putTxnOp o := by
  unfold putTxnOp; split <;> (try split) <;> simp

theorem putTxnOp_ne_delete (o o' : OpFull) : TxnOp.delete o' ≠ putTxnOp o := by
  unfold putTxnOp; split <;> (try split) <;> simp

/-! ## The requests and responses, element by element -/

section iris
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- A range request op. -/
theorem requestOpIs_get (p : Loc) (o : OpFull) :
    requestOpIs (GF := GF) p (.get o) ⊢ ⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestRange.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestRange go!"RequestRange" w ↦□ r ∗
      rangeRequestIs r o := by
  unfold requestOpIs
  iintro #⟨%Hp, %u, %w, %r, %o', #Hu, H⟩
  icases H with (⟨%Hc, #Hw, #Hr⟩ | ⟨%Hc, -, -⟩ | ⟨%Hc, -, -⟩)
  · obtain ⟨rfl, Ho⟩ := Hc
    cases Ho
    isplitl []; · ipureintro; exact Hp
    iexists w, r
    iframe Hu Hw Hr
  · obtain ⟨-, Ho⟩ := Hc
    exact absurd Ho (putTxnOp_ne_get _ _)
  · obtain ⟨-, Ho⟩ := Hc
    cases Ho

/-- A put request op (`op` is a put of the model). -/
theorem requestOpIs_put (p : Loc) (op : TxnOp)
    (hop : (∃ k v l, op = .put k v l) ∨ (∃ k v, op = .putKeep k v) ∨ (∃ k l, op = .putIgnVal k l)) :
    requestOpIs (GF := GF) p op ⊢ ⌜p ≠ null⌝ ∗ ∃ (w r : Loc) (o : OpFull), ⌜op = putTxnOp o⌝ ∗
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestPut go!"RequestPut" w ↦□ r ∗
      putRequestIs r o := by
  have hnt : ∀ cs ts es, op ≠ .txn cs ts es := by
    intro cs ts es h; subst h
    rcases hop with ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
  have hu : requestOpIs (GF := GF) p op = iprop(□ (⌜p ≠ null⌝ ∗ ∃ (u : GoInterface) (w r : Loc) (o : OpFull),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□ u ∗
      ((⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestRange.ty) #w ∧
          op = .get o⌝ ∗
        structFieldRef etcdserverpb.RequestOp_RequestRange go!"RequestRange" w ↦□ r ∗
        rangeRequestIs r o) ∨
       (⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w ∧
          op = putTxnOp o⌝ ∗
        structFieldRef etcdserverpb.RequestOp_RequestPut go!"RequestPut" w ↦□ r ∗
        putRequestIs r o) ∨
       (⌜u = interface.mkOk
            (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w ∧
          op = .delete o⌝ ∗
        structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ r ∗
        deleteRangeRequestIs r o)))) := by
    cases op with
    | txn cs ts es => exact absurd rfl (hnt cs ts es)
    | _ => rfl
  rw [hu]
  iintro #⟨%Hp, %u, %w, %r, %o', #Hu, H⟩
  icases H with (⟨%Hc, -, -⟩ | ⟨%Hc, #Hw, #Hr⟩ | ⟨%Hc, -, -⟩)
  · obtain ⟨-, Ho⟩ := Hc
    subst Ho
    exfalso; rcases hop with ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
  · obtain ⟨rfl, Ho⟩ := Hc
    isplitl []; · ipureintro; exact Hp
    iexists w, r, o'
    iframe Hu Hw Hr
    ipureintro; exact Ho
  · obtain ⟨-, Ho⟩ := Hc
    subst Ho
    exfalso; rcases hop with ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h

/-- A delete request op. -/
theorem requestOpIs_delete (p : Loc) (o : OpFull) :
    requestOpIs (GF := GF) p (.delete o) ⊢ ⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ r ∗
      deleteRangeRequestIs r o := by
  unfold requestOpIs
  iintro #⟨%Hp, %u, %w, %r, %o', #Hu, H⟩
  icases H with (⟨%Hc, -, -⟩ | ⟨%Hc, -, -⟩ | ⟨%Hc, #Hw, #Hr⟩)
  · obtain ⟨-, Ho⟩ := Hc
    cases Ho
  · obtain ⟨-, Ho⟩ := Hc
    exact absurd Ho (putTxnOp_ne_delete _ _)
  · obtain ⟨rfl, Ho⟩ := Hc
    cases Ho
    isplitl []; · ipureintro; exact Hp
    iexists w, r
    iframe Hu Hw Hr

/-- A nested transaction request op. -/
theorem requestOpIs_txn (p : Loc) (cs : List CmpModel) (ts es : List TxnOp) :
    requestOpIs (GF := GF) p (.txn cs ts es) ⊢ ⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestTxn go!"RequestTxn" w ↦□ r ∗
      txnRequestIs r { cmps := cs, thenOps := ts, elseOps := es } := by
  unfold requestOpIs
  iintro #⟨%Hp, %w, %r, #Hu, #Hw, %Hr, %csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm, #Hs,
    #Hss, #Hsm, #Hf, #Hfs, #Hfm⟩
  isplitl []; · ipureintro; exact Hp
  iexists w, r
  iframe Hu Hw
  unfold txnRequestIs txnFieldsIs
  isplitl []; · ipureintro; exact Hr
  iexists csl, ssl, fsl, cps, sps, fps
  iframe Hc Hcs Hcm Hs Hss Hsm Hf Hfs Hfm

/-- The `i`-th request op of a list. -/
theorem requestOpsIs_lookup :
    ∀ (ps : List Loc) (ops : List TxnOp) (i : Nat) (p : Loc) (op : TxnOp),
      ps[i]? = some p → ops[i]? = some op →
      requestOpsIs (GF := GF) ps ops ⊢ requestOpIs p op
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | q :: ps, o :: ops, 0, p, op, hp, hop => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hop
    subst hp hop
    unfold requestOpsIs
    iintro ⟨H, -⟩; iexact H
  | q :: ps, o :: ops, i + 1, p, op, hp, hop => by
    simp only [List.getElem?_cons_succ] at hp hop
    unfold requestOpsIs
    iintro ⟨-, H⟩
    iapply requestOpsIs_lookup ps ops i p op hp hop $$ H

theorem requestOpsIs_length :
    ∀ (ps : List Loc) (ops : List TxnOp), requestOpsIs (GF := GF) ps ops ⊢ ⌜ps.length = ops.length⌝
  | [], [] => by iintro -; ipureintro; rfl
  | _ :: ps, _ :: ops => by
    unfold requestOpsIs
    iintro ⟨-, H⟩
    ihave %h := requestOpsIs_length ps ops $$ H
    ipureintro; simp [h]
  | [], _ :: _ => by unfold requestOpsIs; iintro H; iexfalso; iexact H
  | _ :: _, [] => by unfold requestOpsIs; iintro H; iexfalso; iexact H

/-- The skeletons from the `i`-th on: the `i`-th's, then the rest's. -/
theorem opsSkel_drop (s0 : List EtcdKv) (ps : List Loc) (ops : List TxnOp) (i : Nat) (p : Loc)
    (op : TxnOp) (hp : ps[i]? = some p) (hop : ops[i]? = some op) :
    opsSkel (GF := GF) s0 (ps.drop i) (ops.drop i) ⊣⊢
      opSkel s0 p op ∗ opsSkel s0 (ps.drop (i + 1)) (ops.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 hp).1,
    List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 hop).1,
    (List.getElem?_eq_some_iff.1 hp).2, (List.getElem?_eq_some_iff.1 hop).2]
  rw [opsSkel]
  exact Iris.BI.BIBase.BiEntails.rfl

theorem responseOpsIs_snoc (skip : Bool) :
    ∀ (ps : List Loc) (ops : List TxnOp) (rs : List TxnOpResult) (p : Loc) (op : TxnOp)
      (res : TxnOpResult),
      responseOpsIs (GF := GF) skip ps ops rs ∗ responseOpIs skip p op res ⊢
        responseOpsIs skip (ps ++ [p]) (ops ++ [op]) (rs ++ [res])
  | [], [], [], p, op, res => by
    simp only [List.nil_append]
    unfold responseOpsIs
    iintro ⟨-, H⟩
    unfold responseOpsIs
    iframe H
  | q :: ps, o :: ops, x :: rs, p, op, res => by
    simp only [List.cons_append]
    unfold responseOpsIs
    iintro ⟨⟨Hq, H⟩, Hp⟩
    iframe Hq
    iapply responseOpsIs_snoc skip ps ops rs p op res
    iframe H Hp
  | [], [], _ :: _, _, _, _ => by unfold responseOpsIs; iintro ⟨H, -⟩; iexfalso; iexact H
  | [], _ :: _, _, _, _, _ => by unfold responseOpsIs; iintro ⟨H, -⟩; iexfalso; iexact H
  | _ :: _, [], _, _, _, _ => by unfold responseOpsIs; iintro ⟨H, -⟩; iexfalso; iexact H
  | _ :: _, _ :: _, [], _, _, _ => by unfold responseOpsIs; iintro ⟨H, -⟩; iexfalso; iexact H

theorem responseOpsIs_nil (skip : Bool) : ⊢ responseOpsIs (GF := GF) skip [] [] [] := by
  unfold responseOpsIs; itrivial

/-- A delete keeps the state's leases known. -/
theorem leasesKnown_delete (γl : GName) (r : w64) (s : List EtcdKv) (o : OpFull) :
    leasesKnown (GF := GF) γl s ⊢ leasesKnown γl (mvcc.applyChanges r s (delChanges s o)) := by
  rw [applyChanges_delChanges]
  apply leasesKnown_sub
  intro v hv
  exact (List.mem_filter.1 hv).1

/-- **`executeTxn`'s transaction, by kind**: the kind's facts, its read state the pending one
(for the read-only wrapper, the committed one). -/
theorem txnWriteIs_kind (tw : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (ro : Bool)
    (ilog : mvcc.Log) (pend : List mvcc.Change) :
    txnWriteIs (GF := GF) tw s γ ro ilog pend ⊢ ∃ kind : mvcc.TxnKind, txnViewIs tw s γ kind ro ∗
      ⌜KindIs ro ilog pend kind ∧ KindOk kind ∧ kindState kind = pendState ilog pend ∧
        ilog ≠ [] ∧ ilog.length < 2 ^ 63⌝ := by
  unfold txnWriteIs
  iintro ⟨%kind, Hv, %Hk⟩
  iexists kind
  cases ro
  · unfold KindIs at Hk
    simp only [Bool.false_eq_true, ↓reduceIte] at Hk
    obtain ⟨puts, deletes, putSize, rfl⟩ := Hk
    unfold txnViewIs
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hv with ⟨%mw, %h, Htx⟩
    icases isTxn_kindOk mw s γ _ $$ Htx with ⟨%Hok, Htx⟩
    simp only [mvcc.isTxn]
    icases isTxnWrite_facts mw s γ ilog pend puts deletes putSize $$ Htx with ⟨%Hf, Htx⟩
    isplitl
    · iexists mw; iframe Htx; ipureintro; exact h
    ipureintro
    exact ⟨⟨puts, deletes, putSize, rfl⟩, Hok, kindState_write ilog pend puts deletes putSize Hf.1 Hf.2,
      Hf.1, by have := Hf.2; omega⟩
  · unfold KindIs at Hk
    simp only [↓reduceIte] at Hk
    obtain ⟨rfl, rev, rfl⟩ := Hk
    unfold txnViewIs
    simp only [↓reduceIte]
    icases Hv with ⟨%trw, %log, %rev', %h, Hro⟩
    obtain ⟨h1, h2⟩ := h
    cases h2
    icases isRoTxnWrite_pure trw s γ ilog rev $$ Hro with ⟨Hro, %Hp⟩
    isplitl
    · iexists trw, ilog, rev; iframe Hro; ipureintro; exact ⟨h1, rfl⟩
    ipureintro
    obtain ⟨hok, hne, hrev⟩ := Hp
    refine ⟨⟨rfl, rev, rfl⟩, kindOk_read ilog rev ⟨hok, hne, hrev⟩, ?_, hne, ?_⟩
    · unfold kindState
      simp only [mvcc.TxnKind.readLog, mvcc.TxnKind.readRev]
      rw [hrev, stateAt_lastRev ilog hne (Nat.le_of_lt hok.len)]
      rfl
    · exact hok.len

/-- A transaction of a kind and the kind's facts make `executeTxn`'s. -/
theorem txnWriteIs_of_view (tw : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (ro : Bool)
    (ilog : mvcc.Log) (pend : List mvcc.Change) (kind : mvcc.TxnKind) (h : KindIs ro ilog pend kind) :
    txnViewIs (GF := GF) tw s γ kind ro ⊢ txnWriteIs tw s γ ro ilog pend := by
  unfold txnWriteIs
  iintro Hv
  iexists kind
  iframe Hv
  ipureintro; exact h

/-- **A range of a transaction at its own revision** (revision `0`) at a context never canceled:
no error, the response the client's `rangeKvsOk` of the selection (up to `leaseZ`), the count
the range's. -/
theorem rangeResult_txn (resp : Loc) (err : GoInterface) (log : mvcc.Log) (rev : w64) (o : OpFull)
    (hrev0 : o.base.rev = W64 0) (h0 : 0 ≤ sint.Z rev)
    (hset : o.base.sortSet = decide (o.sortOrder ≠ W64 0 ∨ o.sortTarget ≠ W64 0))
    (hcut : ¬ cutEarly o) (herr : err = GoInterface.nil ∨ sint.Z rev < sint.Z o.base.rev) :
    rangeResult (GF := GF) resp err log rev o true ⊢ ⌜err = GoInterface.nil⌝ ∗
      ∃ (kvs : List EtcdKv) (more : Bool),
        rangeResponseIs resp rev kvs more
          (W64 ((rangeIn (mvcc.stateAt log (sint.nat rev)) o).length : Int)) ∗
        ⌜∃ kvs', rangeKvsOk o (rangeSel (mvcc.stateAt log (sint.nat rev)) o) kvs' ∧
          kvs = kvs'.map (leaseZ (fastKeysOnly o))⌝ := by
  have h00 : sint.Z (W64 0 : w64) = 0 := by decide
  have hRR : mvcc.rangeRev rev o.base.rev = rev := by
    unfold mvcc.rangeRev; rw [hrev0, h00]; simp
  have herr' : err = GoInterface.nil := by
    rcases herr with h | h
    · exact h
    · rw [hrev0, h00] at h; omega
  unfold rangeResult
  iintro (⟨%H, -⟩ | %H | ⟨%H, %kvs, %more, #Hresp, %Hok⟩)
  · rw [hrev0, h00] at H; omega
  · exact absurd herr' H.2.2.2.2
  · rw [hRR] at Hok
    rw [hRR]
    obtain ⟨kvs', h1, h2, -⟩ := srvRangeOk_rangeKvsOk o _ kvs more hset Hok hcut
    isplitl []; · ipureintro; exact herr'
    iexists kvs, more
    have hc : srvCount o (mvcc.stateAt log (sint.nat rev)) true =
        W64 ((rangeIn (mvcc.stateAt log (sint.nat rev)) o).length : Int) := by
      unfold srvCount; split <;> simp [mvcc.totalOf]
    rw [hc]
    iframe Hresp
    ipureintro; exact ⟨kvs', h1, h2⟩

end iris

/-! ## `executeTxn`'s transaction: `Rev` and `Changes` -/

section wp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `executeTxn`'s transaction is an interface value with a dynamic type. -/
theorem txnWriteIs_ok (tw : GoInterface) (s : Loc) (γ : mvcc.StoreNames) (ro : Bool)
    (ilog : mvcc.Log) (pend : List mvcc.Change) :
    txnWriteIs (GF := GF) tw s γ ro ilog pend ⊢ ⌜∃ twi : GoInterfaceOk, tw = GoInterface.ok twi⌝ := by
  unfold txnWriteIs txnViewIs
  iintro ⟨%kind, H, -⟩
  cases ro
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases H with ⟨%mw, %h, -⟩
    ipureintro; exact ⟨_, h⟩
  · simp only [↓reduceIte]
    icases H with ⟨%trw, %log, %rev, %h, -⟩
    ipureintro; exact ⟨_, h.1⟩

/-- **`Rev()` of `executeTxn`'s transaction**: the committed log's last revision. -/
theorem wp_txnWrite_Rev (hRev : mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG))
    (hRoRev : mvcc.txnReadWrite.Rev.spec (GF := GF) (hG := hG))
    (twi : GoInterfaceOk) (s : Loc) (γ : mvcc.StoreNames) (ro : Bool) (ilog : mvcc.Log)
    (pend : List mvcc.Change) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        txnWriteIs (GoInterface.ok twi) s γ ro ilog pend }}
      (App (Val #(methods twi.ty go!"Rev" twi.v)) (Val #()))
    {{ RET #(W64 ((ilog.length : Int) - 1)); txnWriteIs (GoInterface.ok twi) s γ ro ilog pend }} := by
  wp_start_folded as ⟨Htw⟩
  iunfold txnWriteIs at Htw
  icases Htw with ⟨%kind, Hv, %Hk⟩
  cases ro
  · unfold KindIs at Hk
    simp only [Bool.false_eq_true, ↓reduceIte] at Hk
    obtain ⟨puts, deletes, putSize, rfl⟩ := Hk
    iunfold txnViewIs at Hv
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hv with ⟨%mw, %h, Htx⟩
    cases twi with
    | mk ty v =>
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    iapply (hRev mw s γ (.write ilog pend puts deletes putSize)) $$ [Htx]
    · iframe Htx Hpkg
    inext
    iintro Htx
    simp only [mvcc.TxnKind.beginRev]
    iapply HΦ
    iunfold txnWriteIs
    iexists _
    isplitl
    · iapply (txnViewIs_mw mw s γ _).2 $$ Htx
    · ipureintro; exact ⟨puts, deletes, putSize, rfl⟩
  · unfold KindIs at Hk
    simp only [↓reduceIte] at Hk
    obtain ⟨rfl, rev', rfl⟩ := Hk
    iunfold txnViewIs at Hv
    simp only [↓reduceIte]
    icases Hv with ⟨%trw, %log, %rev, %h, Hro⟩
    obtain ⟨h, h2⟩ := h
    cases h2
    cases twi with
    | mk ty v =>
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    iapply (hRoRev trw s γ ilog rev') $$ [Hro]
    · iframe Hro Hpkg
    inext
    iintro ⟨Hro, %Hr⟩
    rw [← Hr.2]
    iapply HΦ
    iunfold txnWriteIs
    iexists _
    isplitl
    · iapply (txnViewIs_ro trw s γ ilog rev').2 $$ Hro
    · ipureintro; exact ⟨rfl, rev', rfl⟩

/-- **`Changes()` of `executeTxn`'s transaction**: as many as the pending changes. -/
theorem wp_txnWrite_Changes (hCh : mvcc.metricsTxnWrite.Changes.spec (GF := GF) (hG := hG))
    (hRoCh : mvcc.txnReadWrite.Changes.spec (GF := GF) (hG := hG))
    (twi : GoInterfaceOk) (s : Loc) (γ : mvcc.StoreNames) (ro : Bool) (ilog : mvcc.Log)
    (pend : List mvcc.Change) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        txnWriteIs (GoInterface.ok twi) s γ ro ilog pend }}
      (App (Val #(methods twi.ty go!"Changes" twi.v)) (Val #()))
    {{ (chs : GoSlice), RET #chs; ⌜sint.nat chs.len = pend.length⌝ ∗
        txnWriteIs (GoInterface.ok twi) s γ ro ilog pend }} := by
  wp_start_folded as ⟨Htw⟩
  iunfold txnWriteIs at Htw
  icases Htw with ⟨%kind, Hv, %Hk⟩
  cases ro
  · unfold KindIs at Hk
    simp only [Bool.false_eq_true, ↓reduceIte] at Hk
    obtain ⟨puts, deletes, putSize, rfl⟩ := Hk
    iunfold txnViewIs at Hv
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hv with ⟨%mw, %h, Htx⟩
    cases twi with
    | mk ty v =>
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    iapply (hCh mw s γ ilog pend puts deletes putSize) $$ [Htx]
    · simp only [mvcc.isTxn] at *; iframe Htx Hpkg
    inext
    iintro %chs ⟨%Hl, Htx⟩
    iapply HΦ
    isplitl []
    · ipureintro; exact Hl
    iunfold txnWriteIs
    iexists _
    isplitl
    · iapply (txnViewIs_mw mw s γ (.write ilog pend puts deletes putSize)).2
      simp only [mvcc.isTxn]; iexact Htx
    · ipureintro; exact ⟨puts, deletes, putSize, rfl⟩
  · unfold KindIs at Hk
    simp only [↓reduceIte] at Hk
    obtain ⟨rfl, rev', rfl⟩ := Hk
    iunfold txnViewIs at Hv
    simp only [↓reduceIte]
    icases Hv with ⟨%trw, %log, %rev, %h, Hro⟩
    obtain ⟨h, h2⟩ := h
    cases h2
    cases twi with
    | mk ty v =>
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    iapply (hRoCh trw) $$ []
    · iframe Hpkg
    inext
    iintro -
    iapply HΦ
    isplitl []
    · ipureintro; rfl
    iunfold txnWriteIs
    iexists _
    isplitl
    · iapply (txnViewIs_ro trw s γ ilog rev').2 $$ Hro
    · ipureintro; exact ⟨rfl, rev', rfl⟩

end wp

end txn
end EtcdGrove
end Perennial
