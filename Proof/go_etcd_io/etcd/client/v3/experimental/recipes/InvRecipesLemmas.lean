/-
Lemmas about the recipes' transactions (`InvRecipesClient.lean`): `putNewKV`'s
(`newKeyTxn`: a put if the key's version is `0`) and `deleteRevKey`'s (`deleteRevTxn`: a delete
if the key's mod revision is `rev`), and what their responses say of etcd's states. Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesClient

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3
open concurrency

/-! ## Puts -/

/-- `OpPut(key, val, WithLease(id))` in a transaction. -/
theorem putLeaseOp_txnOpOf (key val : GoString) (id : w64) :
    txnOpOf (opPutModel key val [withLeaseM id]) = some (.put key val id) := by
  simp [opPutModel, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero, txnOpOf]

theorem putLeaseOp_not_panics (key val : GoString) (id : w64) :
    ¬ (opPutModel key val [withLeaseM id]).putPanics := by
  simp [opPutModel, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero,
    OpFull.putPanics]

/-- `OpPut(key, val)` (no options): a put with no lease. -/
theorem putOp_txnOpOf' (key val : GoString) :
    txnOpOf (opPutModel key val []) = some (.put key val (W64 0)) := by
  simp [opPutModel, opFold, OpFull.putInit, OpFull.newOp, OpModel.zero, txnOpOf]

theorem putOp_not_panics' (key val : GoString) : ¬ (opPutModel key val []).putPanics := by
  simp [opPutModel, opFold, OpFull.putInit, OpFull.newOp, OpModel.zero, OpFull.putPanics]

/-! ## `putNewKV`'s transaction -/

theorem newKeyTxn_under (pfx key val : GoString) (lease : w64) (hk : pfx <+: key) :
    (newKeyTxn key val lease).Under pfx := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp only [newKeyTxn, List.mem_singleton] at hc
    subst hc
    exact keyRangeUnder_key pfx key hk
  · intro op hop
    simp only [newKeyTxn, List.mem_singleton] at hop
    subst hop
    exact hk
  · intro op hop
    simp [newKeyTxn] at hop

/-- The version comparison holds of a missing key. -/
theorem version_cmp_absent (key : GoString) (s : List EtcdKv) (h : ∀ v ∈ s, v.key ≠ key) :
    cmpHolds s (compareM (cmpKeyM .version key) .eq (.num (W64 0))) = true := by
  have : s.filter (fun v => inRange key [] v.key) = [] := by
    rw [List.filter_eq_nil_iff]; intro v hv; simpa [inRange] using h v hv
  simp [cmpHolds, compareM, cmpKeyM, this, cmpKv, zeroKv, int64Cmp, cmpSign, CmpOp.holds]

/-- The version comparison fails on a present key (etcd's versions are positive). -/
theorem version_cmp_present (key : GoString) (s : List EtcdKv)
    (hpos : ∀ v ∈ s, 0 < sint.Z v.version) (h : ∃ v ∈ s, v.key = key) :
    cmpHolds s (compareM (cmpKeyM .version key) .eq (.num (W64 0))) = false := by
  obtain ⟨v, hv, hvk⟩ := h
  have hne : s.filter (fun v => inRange key [] v.key) ≠ [] := by
    intro e
    have : v ∈ s.filter (fun v => inRange key [] v.key) := by
      rw [List.mem_filter]; exact ⟨hv, by simp [inRange, hvk]⟩
    rw [e] at this; simp at this
  simp only [cmpHolds, compareM, cmpKeyM, hne, ite_false]
  rw [List.all_eq_false]
  refine ⟨v, List.mem_filter.2 ⟨hv, by simp [inRange, hvk]⟩, ?_⟩
  have h1 := hpos v hv
  have h2 : v.version ≠ W64 0 := by intro e; rw [e] at h1; simp at h1
  have h3 : ¬ sint.Z v.version < sint.Z (W64 0) := by simp; omega
  simp only [cmpKv, int64Cmp, cmpSign, CmpOp.holds, h2, h3, decide_false]
  decide

/-- **`putNewKV`'s transaction succeeded**: the key was absent (etcd's versions are positive), the
put created it at `r` (a write), with create and mod revision `r`, version `1`, the value and the
lease; the new state is well formed. -/
theorem newKeyTxn_then (pfx key val : GoString) (lease r : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf pfx s) (hk : pfx <+: key) (hpos : ∀ v ∈ s, 0 < sint.Z v.version)
    (h : (runTxn r s (newKeyTxn key val lease)).1 = true) :
    (∀ v ∈ s, v.key ≠ key) ∧ (runTxn r s (newKeyTxn key val lease)).2.1 = putKv r key val lease s ∧
    txnWrote (runTxn r s (newKeyTxn key val lease)).2.2 = true ∧
    EtcdStateWf pfx (putKv r key val lease s) ∧
    ∃ v ∈ putKv r key val lease s, v.key = key ∧ v.createRev = r ∧ v.modRev = r ∧
      v.version = W64 1 ∧ v.value = val ∧ v.lease = lease := by
  have habs : ∀ v ∈ s, v.key ≠ key := by
    intro v hv hvk
    have := version_cmp_present key s hpos ⟨v, hv, hvk⟩
    have h' : (newKeyTxn key val lease).cmps.all (cmpHolds s) = true := h
    simp only [newKeyTxn, List.all_cons, List.all_nil, Bool.and_true] at h'
    rw [this] at h'; cases h'
  have hok : (newKeyTxn key val lease).cmps.all (cmpHolds s) = true := by
    simp only [newKeyTxn, List.all_cons, List.all_nil, Bool.and_true]
    exact version_cmp_absent key s habs
  have e : runTxn r s (newKeyTxn key val lease) = (true, putKv r key val lease s, [.put]) := by
    simp only [runTxn, hok, TxnModel.branch, ite_true]
    simp [newKeyTxn, runOps, applyTxnOp]
  rw [e]
  have hfind : s.find? (fun v => decide (v.key = key)) = none := by
    rw [List.find?_eq_none]; intro v hv; simpa using habs v hv
  refine ⟨habs, rfl, rfl, ⟨?_, ?_⟩, ?_⟩
  · unfold putKv; rw [hfind]
    have h0 : s.Pairwise etcdKvLess :=
      (List.pairwise_map (f := EtcdKv.key) (R := go.GoStringLt)).1 hwf.1
    exact (List.pairwise_map (f := EtcdKv.key) (R := go.GoStringLt)).2
      (btInsert_sorted etcdKvLess_swo h0)
  · unfold putKv; rw [hfind]
    intro v hv
    rcases btInsert_mem hv with rfl | hv
    · exact hk
    · exact hwf.2 v hv
  · unfold putKv; rw [hfind]
    exact ⟨_, btInsert_self_mem _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`putNewKV`'s transaction failed**: the key was present; nothing was written. -/
theorem newKeyTxn_else (key val : GoString) (lease r : w64) (s : List EtcdKv)
    (h : (runTxn r s (newKeyTxn key val lease)).1 = false) :
    (∃ v ∈ s, v.key = key) ∧ (runTxn r s (newKeyTxn key val lease)).2.1 = s ∧
    txnWrote (runTxn r s (newKeyTxn key val lease)).2.2 = false := by
  have hpres : ∃ v ∈ s, v.key = key := by
    refine Classical.byContradiction fun hn => ?_
    have habs : ∀ v ∈ s, v.key ≠ key := fun v hv hvk => hn ⟨v, hv, hvk⟩
    have := version_cmp_absent key s habs
    have h' : (newKeyTxn key val lease).cmps.all (cmpHolds s) = false := h
    simp only [newKeyTxn, List.all_cons, List.all_nil, Bool.and_true] at h'
    rw [this] at h'; cases h'
  have hok : (newKeyTxn key val lease).cmps.all (cmpHolds s) = false := h
  have e : runTxn r s (newKeyTxn key val lease) = (false, s, []) := by
    simp only [runTxn, hok, TxnModel.branch]
    simp [newKeyTxn, runOps]
  rw [e]
  exact ⟨hpres, rfl, rfl⟩

/-! ## `deleteRevKey`'s transaction -/

theorem deleteRevTxn_under (pfx key : GoString) (rev : w64) (hk : pfx <+: key) :
    (deleteRevTxn key rev).Under pfx := by
  obtain ⟨hkk, hke⟩ := deleteOp_fields key
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp only [deleteRevTxn, List.mem_singleton] at hc
    subst hc
    exact keyRangeUnder_key pfx key hk
  · intro op hop
    simp only [deleteRevTxn, List.mem_singleton] at hop
    subst hop
    show KeyRangeUnder pfx (opDeleteModel key []).key (opDeleteModel key []).base.rangeEnd
    rw [hkk, hke]; exact keyRangeUnder_key pfx key hk
  · intro op hop
    simp [deleteRevTxn] at hop

theorem int64Cmp_eq_zero (a b : w64) : int64Cmp a b = 0 ↔ a = b := by
  unfold int64Cmp cmpSign
  by_cases h : a = b
  · subst h; simp
  · have h1 : decide (a = b) = false := decide_eq_false h
    simp only [h1, h, iff_false]
    split <;> simp

/-- **`deleteRevKey`'s transaction succeeded** (for `rev ≠ 0`): the key was present with mod
revision `rev`, the delete removed it (a write), and the state it leaves has no `key`. -/
theorem deleteRevTxn_then (key : GoString) (rev r : w64) (s : List EtcdKv) (hrev : rev ≠ W64 0)
    (h : (runTxn r s (deleteRevTxn key rev)).1 = true) :
    (∃ v ∈ s, v.key = key ∧ v.modRev = rev) ∧
    txnWrote (runTxn r s (deleteRevTxn key rev)).2.2 = true ∧
    ∀ v ∈ (runTxn r s (deleteRevTxn key rev)).2.1, v.key ≠ key := by
  obtain ⟨hkk, hke⟩ := deleteOp_fields key
  have hok : (deleteRevTxn key rev).cmps.all (cmpHolds s) = true := h
  simp only [deleteRevTxn, List.all_cons, List.all_nil, Bool.and_true] at hok
  have hpres : ∃ v ∈ s, v.key = key ∧ v.modRev = rev := by
    unfold cmpHolds at hok
    simp only [compareM, cmpKeyM] at hok
    by_cases hnil : List.filter (fun v => inRange key [] v.key) s = []
    · exfalso
      simp only [hnil, ite_true, cmpKv, zeroKv, CmpOp.holds] at hok
      have : int64Cmp (W64 0) rev = 0 := by simpa using hok
      exact hrev ((int64Cmp_eq_zero _ _).1 this).symm
    · simp only [hnil, ite_false] at hok
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hnil
      have hall := List.all_eq_true.1 hok v hv
      rw [List.mem_filter] at hv
      refine ⟨v, hv.1, by simpa [inRange] using hv.2, ?_⟩
      simp only [cmpKv, CmpOp.holds] at hall
      exact (int64Cmp_eq_zero _ _).1 (by simpa using hall)
  obtain ⟨v, hv, hvk, -⟩ := id hpres
  have hlen : (rangeIn s (opDeleteModel key [])).length ≠ 0 := by
    intro h0
    rw [List.length_eq_zero_iff] at h0
    have : v ∈ rangeIn s (opDeleteModel key []) := by
      unfold rangeIn; rw [List.mem_filter, hkk, hke]; exact ⟨hv, by simp [inRange, hvk]⟩
    rw [h0] at this; simp at this
  have hok' : (deleteRevTxn key rev).cmps.all (cmpHolds s) = true := h
  have e : runTxn r s (deleteRevTxn key rev) =
      (true, s.filter (fun v => !inRange key [] v.key),
        [.delete (rangeIn s (opDeleteModel key [])).length]) := by
    simp only [runTxn, hok', TxnModel.branch, ite_true]
    simp [deleteRevTxn, runOps, applyTxnOp, hkk, hke]
  refine ⟨hpres, ?_, ?_⟩
  · rw [e]; simp [txnWrote, TxnOpResult.wrote, hlen]
  · rw [e]; intro w hw
    rw [List.mem_filter] at hw
    simpa [inRange] using hw.2

/-- **`deleteRevKey`'s transaction failed**: nothing was written. -/
theorem deleteRevTxn_else (key : GoString) (rev r : w64) (s : List EtcdKv)
    (h : (runTxn r s (deleteRevTxn key rev)).1 = false) :
    (runTxn r s (deleteRevTxn key rev)).2.1 = s ∧
    txnWrote (runTxn r s (deleteRevTxn key rev)).2.2 = false := by
  have hok : (deleteRevTxn key rev).cmps.all (cmpHolds s) = false := h
  have e : runTxn r s (deleteRevTxn key rev) = (false, s, []) := by
    simp only [runTxn, hok, TxnModel.branch]
    simp [deleteRevTxn, runOps]
  rw [e]
  exact ⟨rfl, rfl⟩

/-- **`deleteRevKey`'s transaction failed** on a well-formed state: `key` does not have mod
revision `rev` there. -/
theorem deleteRevTxn_else_gone (pfx key : GoString) (rev r : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf pfx s) (h : (runTxn r s (deleteRevTxn key rev)).1 = false) :
    ∀ v ∈ s, v.key = key → v.modRev ≠ rev := by
  intro v hv hvk hm
  have hok : (deleteRevTxn key rev).cmps.all (cmpHolds s) = false := h
  simp only [deleteRevTxn, List.all_cons, List.all_nil, Bool.and_true] at hok
  have hsingle : s.filter (fun w => inRange key [] w.key) = [v] :=
    filter_key_single s hwf.1 key _ (fun w => by simp [inRange]) v hv hvk
  unfold cmpHolds at hok
  simp only [compareM, cmpKeyM, hsingle, List.cons_ne_nil, ite_false, List.all_cons,
    List.all_nil, Bool.and_true, cmpKv, CmpOp.holds] at hok
  have : int64Cmp v.modRev rev = 0 := (int64Cmp_eq_zero _ _).2 hm
  simp [this] at hok

/-! ## The watches -/

/-- `Watch(key, WithRev(rev))` is a single-key watch from `rev` that does not panic. -/
theorem keyWatchOp_fields (key : GoString) (rev : w64) :
    (keyWatchOp key rev).isRangeWatch rev = true ∧ ¬ opWatchPanics key [withRevM rev] ∧
      (keyWatchOp key rev).key = key ∧ (keyWatchOp key rev).base.rangeEnd = [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [keyWatchOp, opWatchModel, opWatchPanics, OpFull.watchPanics, opFold, OpFull.getInit,
    OpFull.newOp, OpModel.zero, withRevM, OpFull.isRangeWatch]

/-- `Watch(kp, WithPrefix(), WithRev(rev))` is a range watch from `rev` that does not panic, of
the keys with prefix `kp` (every key from `"\x00"` for the empty `kp`). -/
theorem prefixWatchOp_fields (kp : GoString) (rev : w64) :
    (prefixWatchOp kp rev).isRangeWatch rev = true ∧
      ¬ opWatchPanics kp [withPrefixM, withRevM rev] ∧
      (kp ≠ [] → (prefixWatchOp kp rev).key = kp ∧
        (prefixWatchOp kp rev).base.rangeEnd = prefixRangeEnd kp) := by
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : kp = [] <;>
    simp [h, prefixWatchOp, opWatchModel, opFold, OpFull.getInit, OpFull.newOp, OpModel.zero,
      withRevM, withPrefixM, OpFull.isRangeWatch]
  · by_cases h : kp = [] <;>
    simp [h, opWatchPanics, OpFull.watchPanics, opWatchModel, opFold, OpFull.getInit,
      OpFull.newOp, OpModel.zero, withRevM, withPrefixM]
  · intro h
    simp [h, prefixWatchOp, opWatchModel, opFold, OpFull.getInit, OpFull.newOp, OpModel.zero,
      withRevM, withPrefixM]

/-- A prefix watch on `kp` is under any prefix `pfx` of `kp`. -/
theorem prefixWatchOp_under (pfx kp : GoString) (rev : w64) (h : pfx <+: kp) :
    KeyRangeUnder pfx (prefixWatchOp kp rev).key (prefixWatchOp kp rev).base.rangeEnd := by
  by_cases hk : kp = []
  · subst hk
    have : pfx = [] := List.prefix_nil.1 h
    subst this
    intro k _; exact List.nil_prefix
  · obtain ⟨-, -, h3⟩ := prefixWatchOp_fields kp rev
    obtain ⟨e1, e2⟩ := h3 hk
    rw [e1, e2]
    intro k hk'
    exact h.trans (keyRangeUnder_prefix kp hk k hk')

section iprop
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- The token of a commit that wrote (`txnCommitResultTok`'s last conjunct). -/
theorem tokIf_true {b : Bool} (h : b = true) (P : IProp GF) :
    (if b then P else iprop(True)) ⊢ P := by
  subst h; exact .rfl

/-- The state before a transaction has positive versions (`etcdState_revs`). -/
theorem txnStates_pos' (pfx : GoString) (r : w64) (s s' : List EtcdKv) (wrote : Bool) :
    txnStates (GF := GF) pfx r s s' wrote ⊢ ⌜∀ v ∈ s, 0 < sint.Z v.version⌝ := by
  unfold txnStates
  split
  · iintro ⟨#H1, -⟩
    ihave %H := etcdState_revs _ _ _ $$ H1
    ipureintro; intro v hv; exact (H v hv).2.2.2
  · iintro #H1
    ihave %H := etcdState_revs _ _ _ $$ H1
    ipureintro; intro v hv; exact (H v hv).2.2.2

/-- A transaction that did not write: `s` is etcd's state at its revision. -/
theorem txnStates_noWrite (pfx : GoString) (r : w64) (s s' : List EtcdKv) (wrote : Bool)
    (hw : wrote = false) :
    txnStates (GF := GF) pfx r s s' wrote ⊢ □ etcdState r pfx s := by
  subst hw
  unfold txnStates
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro #H
  iexact H

/-- A transaction that wrote, leaving `t`: `s` is etcd's state just before its revision, `t` at
it. -/
theorem txnStates_wrote (pfx : GoString) (r : w64) (s s' t : List EtcdKv) (wrote : Bool)
    (hw : wrote = true) (ht : s' = t) :
    txnStates (GF := GF) pfx r s s' wrote ⊢ □ etcdState (r - W64 1) pfx s ∗ □ etcdState r pfx t := by
  subst hw ht
  unfold txnStates
  simp only [↓reduceIte]
  iintro ⟨#H1, #H2⟩
  iframe H1 H2

/-- **A delete event of a single-key watch** (`WaitEvents(c, key, rev, [..., DELETE])`): `key` is
absent at the event's revision, which is at least `rev` and etcd has reached. -/
theorem waitedEvent_key_delete (pfx key : GoString) (rev : w64) (ev : Loc) :
    waitedEvent (GF := GF) pfx (keyWatchOp key rev) rev evDelete ev ⊢
      ∃ r : w64, etcdReached r ∗ etcdAbsent pfx key r ∗ ⌜sint.Z rev ≤ sint.Z r⌝ := by
  obtain ⟨-, -, hk, he⟩ := keyWatchOp_fields key rev
  unfold waitedEvent rangeWatchEvOk
  iintro ⟨%e, -, %Ht, %Hp, #Hr, #Hdel, -⟩
  ihave ⟨#Habs, -⟩ := Hdel $$ %Ht
  have hek : e.key = key := by
    have := Hp.1; rw [hk, he] at this; simpa [inRange] using this
  iexists e.rev
  rw [← hek]
  iframe Hr Habs
  ipureintro; exact Hp.2.1

/-- **A put event** (`WaitEvents`/`WaitPrefixEvents` with `PUT` last): its `*KeyValue` holds the
key-value `v` of the event's key, modified at the event's revision `e.rev` (at least `rev`, etcd
has reached it), which is in etcd's state at `e.rev`; the key is in the watch's range. -/
theorem waitedEvent_put (pfx : GoString) (o : OpFull) (rev : w64) (ev : Loc) :
    waitedEvent (GF := GF) pfx o rev evPut ev ⊢
      ∃ (e : EvModel) (v : EtcdKv) (s : List EtcdKv), eventAt ev e ∗ kvValAt e.kv v ∗
        etcdReached e.rev ∗ □ etcdState e.rev pfx s ∗
        ⌜v ∈ s ∧ EtcdStateWf pfx s ∧ v.key = e.key ∧ v.modRev = e.rev ∧
          sint.Z rev ≤ sint.Z e.rev ∧ inRange o.key o.base.rangeEnd e.key = true⌝ := by
  unfold waitedEvent rangeWatchEvOk
  iintro ⟨%e, #He, %Ht, %Hp, #Hr, -, #Hput⟩
  ihave ⟨%v, #Hv, %Hvk, %s, #Hs, %Hvs⟩ := Hput $$ %Ht
  iexists e, v, s
  iframe He Hv Hr Hs
  ipureintro; exact ⟨Hvs.1, Hvs.2, Hvk.1, Hvk.2, Hp.2.1, Hp.1⟩

/-- The key of a single-key watch's event is the key. -/
theorem waitedEvent_key (pfx key : GoString) (rev : w64) (typ : w32) (ev : Loc) :
    waitedEvent (GF := GF) pfx (keyWatchOp key rev) rev typ ev ⊢
      ∃ e : EvModel, eventAt ev e ∗ ⌜e.key = key ∧ e.typ = typ⌝ := by
  obtain ⟨-, -, hk, he⟩ := keyWatchOp_fields key rev
  unfold waitedEvent rangeWatchEvOk
  iintro ⟨%e, #He, %Ht, %Hp, -, -, -⟩
  iexists e
  iframe He
  ipureintro
  refine ⟨?_, Ht⟩
  have := Hp.1; rw [hk, he] at this; simpa [inRange] using this

end iprop

end recipes
end EtcdGrove
end Perennial
