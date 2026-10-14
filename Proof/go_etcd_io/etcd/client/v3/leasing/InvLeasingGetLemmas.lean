/-
Lemmas for `get`'s acquisition (`kv.go`'s `acquire` and `get`): the acquisition transaction's
model (both branches), the single-key get of the data key (unchanged by the put of its lease
key), and the cache entry built from the acquisition's response. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-! ## The acquisition transaction -/

/-- `acquire`'s transaction for the get `o`, the lease key `lk` and the lease `id`: if the lease
key was never created and the data key has no lease, `o` and put the lease key with `id`; else
`o` and get the lease key. -/
def acquireTxn (key lk : GoString) (id : w64) (o : OpFull) : TxnModel :=
  { cmps := [compareM (cmpKeyM .create lk) .eq (.num (W64 0)),
             compareM (cmpKeyM .lease key) .eq (.num (W64 0))],
    thenOps := [.get o, .put lk [] id],
    elseOps := [.get o, .get (opGetModel lk [])] }

theorem acquireTxn_linearizable (key lk : GoString) (id : w64) (o : OpFull) :
    (acquireTxn key lk id o).linearizable = true := by
  simp [acquireTxn, TxnModel.linearizable, TxnOp.linearizable]

/-- A filter that selects no key of `nv`'s is unchanged by inserting `nv`. -/
theorem filter_btInsert (nv : EtcdKv) (s : List EtcdKv) (p : EtcdKv → Bool)
    (hp : ∀ v, p v = true → v.key ≠ nv.key) :
    (btInsert etcdKvLess nv s).filter p = s.filter p := by
  induction s with
  | nil =>
    have : p nv = false := by
      cases h : p nv
      · rfl
      · exact absurd rfl (hp nv h)
    simp [btInsert, this]
  | cons w ws ih =>
    have hnv : p nv = false := by
      cases h : p nv
      · rfl
      · exact absurd rfl (hp nv h)
    unfold btInsert
    split
    · rw [List.filter_cons, List.filter_cons, ih]
    · split
      · rw [List.filter_cons, hnv]; simp
      · rename_i h1 h2
        have he : w.key = nv.key := goStringLt_eq_of_not_lt h1 h2
        have hw : p w = false := by
          cases h : p w
          · rfl
          · exact absurd he (hp w h)
        rw [List.filter_cons, hnv, List.filter_cons, hw]; simp

/-- The put `putKv r lk val l s` changes no key but `lk`. -/
theorem filter_putKv (r : w64) (lk val : GoString) (l : w64) (s : List EtcdKv)
    (p : EtcdKv → Bool) (hp : ∀ v, p v = true → v.key ≠ lk) :
    (putKv r lk val l s).filter p = s.filter p := by
  unfold putKv
  apply filter_btInsert
  intro v hv
  split
  · rename_i v' hf
    have := List.find?_some hf
    simp at this
    simpa [this] using hp v hv
  · simpa using hp v hv

/-- A get of the key `key` alone reads the same before and after a put of another key. -/
theorem rangeSel_putKv (r : w64) (lk val : GoString) (l : w64) (s : List EtcdKv) (o : OpFull)
    (hk : o.base.rangeEnd = []) (hne : o.key ≠ lk) :
    rangeSel (putKv r lk val l s) o = rangeSel s o ∧
      (rangeIn (putKv r lk val l s) o).length = (rangeIn s o).length := by
  have hp : ∀ v : EtcdKv, inRange o.key o.base.rangeEnd v.key = true → v.key ≠ lk := by
    intro v hv; rw [hk] at hv; simp [inRange] at hv; rw [hv]; exact hne
  have h1 : rangeIn (putKv r lk val l s) o = rangeIn s o := by
    unfold rangeIn; exact filter_putKv r lk val l s _ hp
  refine ⟨?_, by rw [h1]⟩
  unfold rangeSel; rw [h1]

/-- The put of `lk` keeps the state well formed and holds the new record. -/
theorem putKv_wf (r : w64) (lk val : GoString) (l : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf [] s) :
    EtcdStateWf [] (putKv r lk val l s) ∧ ∃ nv : EtcdKv, kvOf (putKv r lk val l s) lk = some nv ∧
      nv.lease = l := by
  have h0 : s.Pairwise etcdKvLess :=
    (List.pairwise_map (f := EtcdKv.key) (R := go.GoStringLt)).1 hwf.1
  have hwf' : EtcdStateWf [] (putKv r lk val l s) := by
    refine ⟨?_, fun v _ => List.nil_prefix⟩
    unfold putKv
    exact (List.pairwise_map (f := EtcdKv.key) (R := go.GoStringLt)).2
      (btInsert_sorted etcdKvLess_swo h0)
  refine ⟨hwf', ?_⟩
  cases hf : s.find? (fun v => decide (v.key = lk)) with
  | some v' =>
    have hk := List.find?_some hf
    simp at hk
    let nv : EtcdKv := { v' with modRev := r, version := v'.version + W64 1, value := val, lease := l }
    have he : putKv r lk val l s = btInsert etcdKvLess nv s := by simp [putKv, hf, nv]
    rw [he] at hwf' ⊢
    refine ⟨nv, ?_, rfl⟩
    have := kvOf_of_mem _ _ hwf' (concurrency.btInsert_self_mem nv s)
    simpa [nv, hk] using this
  | none =>
    let nv : EtcdKv := { key := lk, createRev := r, modRev := r, version := W64 1, value := val, lease := l }
    have he : putKv r lk val l s = btInsert etcdKvLess nv s := by simp [putKv, hf, nv]
    rw [he] at hwf' ⊢
    refine ⟨nv, ?_, rfl⟩
    have := kvOf_of_mem _ _ hwf' (concurrency.btInsert_self_mem nv s)
    simpa [nv] using this

/-- **The acquisition transaction, by branch**: its result's comparisons, state and results. -/
theorem acquireTxn_run (key lk : GoString) (id r : w64) (o : OpFull) (s : List EtcdKv) :
    (runTxn r s (acquireTxn key lk id o)).1 = true ∧
      (runTxn r s (acquireTxn key lk id o)).2.1 = putKv r lk [] id s ∧
      (runTxn r s (acquireTxn key lk id o)).2.2 =
        [.range (rangeSel s o) (rangeIn s o).length, .put] ∧
      txnWrote (runTxn r s (acquireTxn key lk id o)).2.2 = true ∨
    (runTxn r s (acquireTxn key lk id o)).1 = false ∧
      (runTxn r s (acquireTxn key lk id o)).2.1 = s ∧
      (runTxn r s (acquireTxn key lk id o)).2.2 =
        [.range (rangeSel s o) (rangeIn s o).length,
         .range (rangeSel s (opGetModel lk [])) (rangeIn s (opGetModel lk [])).length] ∧
      txnWrote (runTxn r s (acquireTxn key lk id o)).2.2 = false := by
  cases h : (acquireTxn key lk id o).cmps.all (cmpHolds s)
  · right
    simp only [runTxn, h, TxnModel.branch]
    simp [acquireTxn, runOps, applyTxnOp, txnWrote, TxnOpResult.wrote]
  · left
    simp only [runTxn, h, TxnModel.branch]
    simp [acquireTxn, runOps, applyTxnOp, txnWrote, TxnOpResult.wrote]

/-- **The single-key get `OpGet(key)` lists the key's record** (`kvOf`), in a well-formed state. -/
theorem keyGet_kvs (key : GoString) (s kvs : List EtcdKv) (hwf : EtcdStateWf [] s)
    (h : rangeKvsOk (opGetModel key []) (rangeSel s (opGetModel key [])) kvs) :
    kvs = (kvOf s key).toList := by
  obtain ⟨h1, h2⟩ := concurrency.keyOp_kvs [] key s kvs hwf h
  cases hk : kvOf s key with
  | none =>
    simp only [Option.toList_none]
    apply h1
    intro v hv hvk
    have := kvOf_of_mem s v hwf hv
    rw [hvk, hk] at this; cases this
  | some v =>
    obtain ⟨hv, hvk⟩ := kvOf_mem hk
    simp only [Option.toList_some]
    exact h2 v hv hvk

/-- The first cached key-value of a single-key get's response is the key's record. -/
theorem keyGet_head (key : GoString) (s : List EtcdKv) (cs : List CachedKv)
    (hwf : EtcdStateWf [] s)
    (h : rangeKvsOk (opGetModel key []) (rangeSel s (opGetModel key [])) (cs.map CachedKv.kv)) :
    (cs.head?).map CachedKv.kv = kvOf s key := by
  have hk := keyGet_kvs key s _ hwf h
  rcases cs with _ | ⟨c, cs⟩
  · cases hkv : kvOf s key with
    | none => rfl
    | some v => rw [hkv] at hk; simp at hk
  · cases hkv : kvOf s key with
    | none => rw [hkv] at hk; simp at hk
    | some v =>
      rw [hkv] at hk
      simp only [List.map_cons, Option.toList_some, List.cons.injEq] at hk
      simp [hk.1]

theorem keyGet_txnOpOf (key : GoString) :
    txnOpOf (opGetModel key []) = some (.get (opGetModel key [])) :=
  concurrency.keyOp_txnOpOf key

theorem keyGet_fields (key : GoString) :
    (opGetModel key []).t = W64 1 ∧ (opGetModel key []).key = key ∧
    (opGetModel key []).base.rangeEnd = [] ∧ (opGetModel key []).base.rev = W64 0 ∧
    (opGetModel key []).base.serializable = false :=
  concurrency.keyOp_t key

theorem leasePut_txnOpOf (lk : GoString) (id : w64) :
    txnOpOf (opPutModel lk [] [withLeaseM id]) = some (.put lk [] id) :=
  concurrency.putOp_txnOpOf lk id

theorem leasePut_not_panics (lk : GoString) (id : w64) :
    ¬ (opPutModel lk [] [withLeaseM id]).putPanics :=
  concurrency.putOp_not_panics lk id

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]

theorem txnStates_wrote (pfx : GoString) (r : w64) (s s' : List EtcdKv) :
    txnStates (GF := GF) pfx r s s' true ⊢ □ etcdState (r - W64 1) pfx s ∗ □ etcdState r pfx s' := by
  unfold txnStates
  simp only [↓reduceIte]
  iintro ⟨#H1, #H2⟩
  iframe #

theorem txnStates_read (pfx : GoString) (r : w64) (s s' : List EtcdKv) :
    txnStates (GF := GF) pfx r s s' false ⊢ □ etcdState r pfx s := by
  unfold txnStates
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro #H
  iexact H

/-- Owned responses of two operations. -/
theorem txnOpsRespOwn_two (p0 p1 : Loc) (a b : TxnOp) (x y : TxnOpResult) :
    txnOpsRespOwn (GF := GF) [p0, p1] [a, b] [x, y] ⊢ txnOpRespOwn p0 a x ∗ txnOpRespOwn p1 b y := by
  simp only [txnOpsRespOwn]
  iintro ⟨H0, H1, -⟩
  iframe

/-- Owned responses of two operations: two responses. -/
theorem txnOpsRespOwn_len2 (ps : List Loc) (a b : TxnOp) (x y : TxnOpResult) :
    txnOpsRespOwn (GF := GF) ps [a, b] [x, y] ⊢ ∃ p0 p1, ⌜ps = [p0, p1]⌝ ∗
      txnOpsRespOwn [p0, p1] [a, b] [x, y] := by
  rcases ps with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, ps⟩⟩⟩
  · simp only [txnOpsRespOwn]; iintro %H; exact H.elim
  · simp only [txnOpsRespOwn]; iintro ⟨-, %H⟩; exact H.elim
  · iintro H; iexists p0, p1; iframe; ipureintro; rfl
  · simp only [txnOpsRespOwn]; iintro ⟨-, -, %H⟩; exact H.elim

/-- An owned get response (`txnOpRespOwn`), opened. -/
theorem txnOpRespOwn_get (p : Loc) (o : OpFull) (sel : List EtcdKv) (n : Nat) :
    txnOpRespOwn (GF := GF) p (.get o) (.range sel n) ⊣⊢ iprop(⌜p ≠ null⌝ ∗ ∃ (w rr : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ rr ∗
      ⌜rr ≠ null⌝ ∗ rangeRespOwn rr o sel n) := by
  simp only [txnOpRespOwn]
  exact .rfl

end lemmas

end leasing
end EtcdGrove
end Perennial
