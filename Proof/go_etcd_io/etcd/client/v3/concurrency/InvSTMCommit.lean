/-
Lemmas of the STM's commits (`stm.commit`, `stmSerializable.commit`): what a successful commit's
transaction gives (`stmCommit_outcome`: `stmOutcome`, in particular `ReadsAgree` from the read
keys' comparisons and the history law `etcdState_modrev_det`), the transaction is under the
prefix, and the `Else` gets' responses of a failed `stmSerializable.commit` are reads
(`respOpReadAt`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTM

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

/-! ## Pure lemmas -/

theorem kvAt_some {s : List EtcdKv} {k : GoString} {w : EtcdKv} (h : kvAt s k = some w) :
    w ∈ s ∧ w.key = k := by
  unfold kvAt at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem kvAt_none {s : List EtcdKv} {k : GoString} (h : kvAt s k = none) :
    ∀ v ∈ s, v.key ≠ k := by
  unfold kvAt at h
  intro v hv
  simpa using List.find?_eq_none.1 h v hv

theorem int64Cmp_eq {a b : w64} (h : (int64Cmp a b == 0) = true) : a = b := by
  unfold int64Cmp cmpSign at h
  by_cases h1 : sint.Z a < sint.Z b
  · simp [h1] at h
  · by_cases h2 : a = b
    · exact h2
    · simp [h1, h2] at h

theorem int64Cmp_lt {a b : w64} (h : decide (int64Cmp a b < 0) = true) :
    sint.Z a < sint.Z b := by
  unfold int64Cmp cmpSign at h
  by_cases h1 : sint.Z a < sint.Z b
  · exact h1
  · by_cases h2 : a = b <;> simp [h1, h2] at h

/-- The single-key comparison `c` (key `k`, no range end) holding on `s`: of `k`'s key-value
if present, of the zero key-value otherwise. -/
theorem cmpHolds_key (s : List EtcdKv) (c : CmpModel) (hk : c.rangeEnd = []) (h : cmpHolds s c = true) :
    (∀ w, kvAt s c.key = some w → cmpKv c w = true) ∧
      (kvAt s c.key = none → cmpKv c (zeroKv c.key) = true) := by
  unfold cmpHolds at h
  simp only [hk] at h
  refine ⟨fun w hw => ?_, fun hn => ?_⟩
  · obtain ⟨hws, hwk⟩ := kvAt_some hw
    have hm : w ∈ s.filter (fun v => inRange c.key [] v.key) :=
      List.mem_filter.2 ⟨hws, by simp [inRange, hwk]⟩
    have hne : s.filter (fun v => inRange c.key [] v.key) ≠ [] := List.ne_nil_of_mem hm
    simp only [hne, ite_false, List.all_eq_true] at h
    exact h w hm
  · have he : s.filter (fun v => inRange c.key [] v.key) = [] := by
      rw [List.filter_eq_nil_iff]
      intro v hv
      simpa [inRange] using kvAt_none hn v hv
    simp only [he, ite_true, Bool.and_eq_true] at h
    exact h.2

/-- A read's comparison (`isKeyCurrent`) holding on `s`. -/
theorem readCmp_holds (s : List EtcdKv) (k : GoString) (e : ReadM)
    (h : cmpHolds s (readCmp k e) = true) :
    (∀ w, kvAt s k = some w → w.modRev = e.modRev) ∧ (kvAt s k = none → e.modRev = W64 0) := by
  obtain ⟨h1, h2⟩ := cmpHolds_key s (readCmp k e) (by simp [readCmp, compareM, cmpKeyM]) h
  refine ⟨fun w hw => ?_, fun hn => ?_⟩
  · have := h1 w (by simpa [readCmp, compareM, cmpKeyM] using hw)
    simp only [readCmp, compareM, cmpKeyM, cmpKv, CmpOp.holds] at this
    exact int64Cmp_eq this
  · have := h2 (by simpa [readCmp, compareM, cmpKeyM] using hn)
    simp only [readCmp, compareM, cmpKeyM, cmpKv, CmpOp.holds, zeroKv] at this
    exact (int64Cmp_eq this).symm

/-- A written key's comparison (`writeSet.cmps`) holding on `s`. -/
theorem writeCmp_holds (s : List EtcdKv) (rev : w64) (k : GoString)
    (h : cmpHolds s (writeCmp rev k) = true) : sint.Z (modRevAt s k) < sint.Z rev := by
  obtain ⟨h1, h2⟩ := cmpHolds_key s (writeCmp rev k) (by simp [writeCmp, compareM, cmpKeyM]) h
  unfold modRevAt
  cases hk : kvAt s k with
  | some w =>
    have := h1 w (by simpa [writeCmp, compareM, cmpKeyM] using hk)
    simp only [writeCmp, compareM, cmpKeyM, cmpKv, CmpOp.holds] at this
    simpa using int64Cmp_lt this
  | none =>
    have := h2 (by simpa [writeCmp, compareM, cmpKeyM] using hk)
    simp only [writeCmp, compareM, cmpKeyM, cmpKv, CmpOp.holds, zeroKv] at this
    simpa using int64Cmp_lt this

theorem readCmpsOk_mem {reads : GMap GoString ReadM} {ms : List CmpModel}
    (h : ReadCmpsOk reads ms) {k : GoString} {e : ReadM} (he : reads !! k = some e) :
    readCmp k e ∈ ms := by
  obtain ⟨ks, ⟨-, hks⟩, rfl⟩ := h
  rw [List.mem_filterMap]
  exact ⟨k, (hks k).2 (by simp [he]), by simp [he]⟩

theorem writeCmpsOk_mem {writes : GMap GoString WriteM} {rev : w64} {ms : List CmpModel}
    (h : WriteCmpsOk writes rev ms) {k : GoString} (hk : (writes !! k).isSome) :
    writeCmp rev k ∈ ms := by
  obtain ⟨ks, ⟨-, hks⟩, rfl⟩ := h
  exact List.mem_map.2 ⟨k, (hks k).2 hk, rfl⟩

theorem writeOpsOk_mem {writes : GMap GoString WriteM} {ops : List TxnOp}
    (h : WriteOpsOk writes ops) {op : TxnOp} (hop : op ∈ ops) :
    ∃ k w, writes !! k = some w ∧ op = w.op k := by
  obtain ⟨ks, -, rfl⟩ := h
  rw [List.mem_filterMap] at hop
  obtain ⟨k, -, hk⟩ := hop
  cases hw : writes !! k with
  | none => simp [hw] at hk
  | some w => simp [hw] at hk; exact ⟨k, w, hw, hk.symm⟩

/-- A commit with a write is linearizable. -/
theorem writeOps_linearizable {writes : GMap GoString WriteM} {ops : List TxnOp}
    (ms : List CmpModel) (eops : List TxnOp) (h : WriteOpsOk writes ops) (hne : ops ≠ []) :
    ({ cmps := ms, thenOps := ops, elseOps := eops } : TxnModel).linearizable = true := by
  obtain ⟨op, hop⟩ := List.exists_mem_of_ne_nil ops hne
  obtain ⟨k, w, -, rfl⟩ := writeOpsOk_mem h hop
  unfold TxnModel.linearizable
  rw [List.any_eq_true]
  refine ⟨w.op k, List.mem_append_left _ hop, ?_⟩
  cases w <;> rfl

/-- The comparisons and writes of an attempt are under the prefix. -/
theorem stmTxn_under (pfx : GoString) (lvl : w64) {reads : GMap GoString ReadM}
    {writes : GMap GoString WriteM} {ms : List CmpModel} {ops eops : List TxnOp}
    (hr : ∀ k e, reads !! k = some e → pfx <+: k) (hw : ∀ k, (writes !! k).isSome → pfx <+: k)
    (hcf : ConflictsOk lvl reads writes ms) (hops : WriteOpsOk writes ops)
    (heops : ∀ op ∈ eops, op.Under pfx) :
    TxnModel.Under pfx { cmps := ms, thenOps := ops, elseOps := eops } := by
  refine ⟨?_, ?_, heops⟩
  · have hrc : ∀ m1, ReadCmpsOk reads m1 → ∀ c ∈ m1, KeyRangeUnder pfx c.key c.rangeEnd := by
      rintro m1 ⟨ks, -, rfl⟩ c hc
      rw [List.mem_filterMap] at hc
      obtain ⟨k, -, hk⟩ := hc
      cases he : reads !! k with
      | none => simp [he] at hk
      | some e =>
        simp [he] at hk; subst hk
        exact keyRangeUnder_key pfx k (hr k e he)
    rcases hcf with ⟨-, f, m1, m2, -, h1, ⟨ks, ⟨-, hks⟩, rfl⟩, rfl⟩ | ⟨-, h⟩ | ⟨-, rfl⟩
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact hrc m1 h1 c hc
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
        exact keyRangeUnder_key pfx k (hw k ((hks k).1 hk))
    · exact hrc ms h
    · simp
  · intro op hop
    obtain ⟨k, w, hkw, rfl⟩ := writeOpsOk_mem hops hop
    have hk := hw k (by simp [hkw])
    cases w with
    | put v l => exact hk
    | del =>
      obtain ⟨h1, h2⟩ := deleteOp_fields k
      show KeyRangeUnder pfx (opDeleteModel k []).key (opDeleteModel k []).base.rangeEnd
      rw [h1, h2]; exact keyRangeUnder_key pfx k hk

/-- **The reads agree with the state the commit ran on**: each read key's comparison holds on
`s`, and each read is (by the mod revision history law) a key-value of `s` or absent. -/
theorem readsAgree_of (reads : GMap GoString ReadM) (s : List EtcdKv)
    (hpos : ∀ v ∈ s, 0 < sint.Z v.modRev)
    (hcmp : ∀ k e, reads !! k = some e → cmpHolds s (readCmp k e) = true)
    (hfact : ∀ k e, reads !! k = some e → ∃ s0 : List EtcdKv, kvAt s0 k = e.kv ∧
      (∀ v ∈ s0, 0 < sint.Z v.modRev) ∧
      (∀ v ∈ s0, ∀ v' ∈ s, v.key = v'.key → v.modRev = v'.modRev → v = v')) :
    ReadsAgree reads s := by
  intro k e he
  obtain ⟨h1, h2⟩ := readCmp_holds s k e (hcmp k e he)
  obtain ⟨s0, hs0, hpos0, hdet⟩ := hfact k e he
  cases hk : kvAt s k with
  | none =>
    have hm := h2 hk
    cases hek : e.kv with
    | none => rfl
    | some v0 =>
      rw [hek] at hs0
      have := hpos0 v0 (kvAt_some hs0).1
      simp [ReadM.modRev, hek] at hm
      rw [hm] at this; simp at this
  | some w =>
    have hm := h1 w hk
    obtain ⟨hws, hwk⟩ := kvAt_some hk
    have hw0 := hpos w hws
    cases hek : e.kv with
    | none =>
      simp [ReadM.modRev, hek] at hm
      rw [hm] at hw0; simp at hw0
    | some v0 =>
      rw [hek] at hs0
      obtain ⟨hv0, hv0k⟩ := kvAt_some hs0
      simp only [ReadM.modRev, hek] at hm
      rw [hdet v0 hv0 w hws (by rw [hv0k, hwk]) hm.symm]

/-! ## The `Else` gets of `stmSerializable.commit` -/

/-- Gets leave the state unchanged. -/
theorem runOps_gets (r : w64) (s : List EtcdKv) (l : List OpFull) :
    runOps r s (l.map TxnOp.get) =
      (s, l.map (fun o => TxnOpResult.range (rangeSel s o) (rangeIn s o).length)) := by
  induction l with
  | nil => rfl
  | cons o l ih => simp only [List.map_cons, runOps, applyTxnOp, ih]

theorem txnWrote_gets (s : List EtcdKv) (l : List OpFull) :
    txnWrote (l.map (fun o => TxnOpResult.range (rangeSel s o) (rangeIn s o).length)) = false := by
  unfold txnWrote
  rw [List.any_eq_false]
  intro x hx
  obtain ⟨o, -, rfl⟩ := List.mem_map.1 hx
  simp [TxnOpResult.wrote]

/-- The `Else` gets of the read keys: `OpGet(k)` each, under the prefix. -/
theorem keyOps_under (pfx : GoString) (ks : List GoString) (hks : ∀ k ∈ ks, pfx <+: k) :
    ∀ op ∈ (ks.map keyOp).map TxnOp.get, op.Under pfx := by
  intro op hop
  rw [List.map_map, List.mem_map] at hop
  obtain ⟨k, hk, rfl⟩ := hop
  obtain ⟨-, hkk, hke, -, -⟩ := keyOp_t k
  show KeyRangeUnder pfx (keyOp k).key (keyOp k).base.rangeEnd
  rw [hkk, hke]; exact keyRangeUnder_key pfx k (hks k hk)

theorem keyOps_txnOpOf (ks : List GoString) :
    (ks.map keyOp).map txnOpOf = ((ks.map keyOp).map TxnOp.get).map some := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro k _
  simp [keyOp_txnOpOf]

/-! ## Separation logic -/

theorem pure_forall_intro {PROP : Type _} [BI PROP] {P : PROP} {α : Sort _} {φ : α → Prop}
    (h : ∀ x, P ⊢ ⌜φ x⌝) : P ⊢ ⌜∀ x, φ x⌝ :=
  (forall_intro h).trans pure_forall.2

section iprop
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- The state a transaction ran on is etcd's state at some revision. -/
theorem txnStates_before (pfx : GoString) (r : w64) (s s' : List EtcdKv) (w : Bool) :
    txnStates (GF := GF) pfx r s s' w ⊢ ∃ a, □ etcdState a pfx s := by
  unfold txnStates
  split
  · iintro ⟨#H1, -⟩
    iexists _; iexact H1
  · iintro #H1
    iexists _; iexact H1

/-- A transaction that did not write: the state it ran on is etcd's at its revision. -/
theorem txnStates_noWrite (pfx : GoString) (r : w64) (s s' : List EtcdKv) :
    txnStates (GF := GF) pfx r s s' false ⊢ □ etcdState r pfx s := by
  unfold txnStates
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro #H
  iexact H

theorem readsAt_readFacts (pfx : GoString) (rsMap : GMap GoString Loc)
    (reads : GMap GoString ReadM) : readsAt (GF := GF) pfx rsMap reads ⊢ readFacts pfx reads := by
  unfold readsAt readFacts
  iintro ⟨%Hk, #H⟩
  imodintro
  iintro %k %e %he
  obtain ⟨p, hp⟩ : ∃ p, rsMap !! k = some p := by
    have := Hk k
    rw [he] at this
    cases h : rsMap !! k with
    | none => rw [h] at this; simp at this
    | some p => exact ⟨p, rfl⟩
  ihave Hr := H $$ %k %p %e %hp %he
  iunfold readRespAt at Hr
  icases Hr with ⟨-, #Hf, -, -⟩
  iexact Hf

theorem readFacts_under (pfx : GoString) (reads : GMap GoString ReadM) :
    readFacts (GF := GF) pfx reads ⊢ ⌜∀ k e, reads !! k = some e → pfx <+: k⌝ := by
  apply pure_forall_intro; intro k
  apply pure_forall_intro; intro e
  apply pure_forall_intro; intro he
  unfold readFacts
  iintro #H
  ihave Hf := H $$ %k %e %he
  iunfold readFact at Hf
  icases Hf with ⟨%s0, -, %Hw⟩
  ipureintro; exact Hw.2.2

theorem writesAt_under (pfx : GoString) (wsMap : GMap GoString stmPut)
    (writes : GMap GoString WriteM) :
    writesAt (GF := GF) pfx wsMap writes ⊢ ⌜∀ k, (writes !! k).isSome → pfx <+: k⌝ := by
  apply pure_forall_intro; intro k
  apply pure_forall_intro; intro hk
  obtain ⟨w, hw⟩ : ∃ w, writes !! k = some w := Option.isSome_iff_exists.1 hk
  unfold writesAt
  iintro ⟨%Hk, #H⟩
  obtain ⟨sp, hsp⟩ : ∃ sp, wsMap !! k = some sp := by
    have := Hk k
    rw [hw] at this
    exact Option.isSome_iff_exists.1 (by simpa using this)
  ihave Hf := H $$ %k %sp %w %hsp %hw
  iunfold writeAt at Hf
  icases Hf with ⟨%Hw, -⟩
  ipureintro; exact Hw.2

/-- The reads' facts, against the state `s` (etcd's at `a`): each read key-value is its key's
in a state with positive mod revisions, which agrees with `s` on mod revisions. -/
theorem readFacts_det (pfx : GoString) (reads : GMap GoString ReadM) (a : w64)
    (s : List EtcdKv) :
    □ etcdState (GF := GF) a pfx s ∗ readFacts pfx reads ⊢
      ⌜∀ k e, reads !! k = some e → ∃ s0 : List EtcdKv, kvAt s0 k = e.kv ∧
        (∀ v ∈ s0, 0 < sint.Z v.modRev) ∧
        (∀ v ∈ s0, ∀ v' ∈ s, v.key = v'.key → v.modRev = v'.modRev → v = v')⌝ := by
  apply pure_forall_intro; intro k
  apply pure_forall_intro; intro e
  apply pure_forall_intro; intro he
  unfold readFacts
  iintro ⟨#Hs, #H⟩
  ihave Hf := H $$ %k %e %he
  iunfold readFact at Hf
  icases Hf with ⟨%s0, #Hs0, %Hw⟩
  ihave %Hrevs := etcdState_revs _ _ _ $$ Hs0
  ihave %Hdet := etcdState_modrev_det e.rev a pfx s0 s $$ [Hs0 Hs]
  · isplitr
    · iexact Hs0
    · iexact Hs
  ipureintro
  refine ⟨s0, Hw.2.1, fun v hv => ?_, Hdet⟩
  obtain ⟨h1, h2, -, -⟩ := Hrevs v hv
  omega

/-- **A successful commit**: the transaction `If(ms...).Then(ops...).Else(eops...)` of the
attempt `st` (the level's conflicts, the writes' operations) succeeded at revision `r` on `s`:
`stmOutcome`. -/
theorem stmCommit_outcome (pfx : GoString) (lvl lo : w64) (st : STMSt) (resp : Loc)
    (ms : List CmpModel) (ops eops : List TxnOp) (r : w64) (s : List EtcdKv)
    (hok : (runTxn r s { cmps := ms, thenOps := ops, elseOps := eops }).1 = true)
    (hcf : ConflictsOk lvl st.reads st.writes ms) (hops : WriteOpsOk st.writes ops)
    (hlin : ({ cmps := ms, thenOps := ops, elseOps := eops } : TxnModel).linearizable = true →
      sint.Z lo ≤ sint.Z r)
    (hr0 : 0 < sint.Z r) (hrmax : sint.Z r < 2 ^ 63 - 1) (hwf : EtcdStateWf pfx s) :
    readFacts (GF := GF) pfx st.reads ∗ etcdReached r ∗
      txnStates pfx r s (runTxn r s { cmps := ms, thenOps := ops, elseOps := eops }).2.1
        (txnWrote (runTxn r s { cmps := ms, thenOps := ops, elseOps := eops }).2.2) ∗
      txnRespAt resp r (runTxn r s { cmps := ms, thenOps := ops, elseOps := eops }).1
        (({ cmps := ms, thenOps := ops, elseOps := eops } : TxnModel).branch
          (runTxn r s { cmps := ms, thenOps := ops, elseOps := eops }).1)
        (runTxn r s { cmps := ms, thenOps := ops, elseOps := eops }).2.2 ⊢
      stmOutcome pfx lvl lo st resp := by
  have hall : ms.all (cmpHolds s) = true := hok
  have hrun : runTxn r s { cmps := ms, thenOps := ops, elseOps := eops } =
      (true, (runOps r s ops).1, (runOps r s ops).2) := by
    simp only [runTxn, hall, TxnModel.branch, ite_true]
  have hbr : ({ cmps := ms, thenOps := ops, elseOps := eops } : TxnModel).branch true = ops := rfl
  rw [hrun, hbr]
  have hc : ∀ c ∈ ms, cmpHolds s c = true := List.all_eq_true.1 hall
  iintro ⟨#Hf, #Hr, #Hts, #Hresp⟩
  ihave ⟨%a, #Hs⟩ := txnStates_before pfx r s _ _ $$ Hts
  ihave %Hrevs := etcdState_revs _ _ _ $$ Hs
  ihave %Hfacts := readFacts_det pfx st.reads a s $$ [Hs Hf]
  · isplitr
    · imodintro; iexact Hs
    · iexact Hf
  unfold stmOutcome
  iexists r, s, (runOps r s ops).1, ops
  iframe Hts Hr Hf Hresp
  ipureintro
  refine ⟨hwf, rfl, hops, fun hne => hlin (writeOps_linearizable ms eops hops hne), hr0, hrmax,
    fun hrc => ?_, fun hss => ?_⟩
  · have hm1 : ∃ m1, ReadCmpsOk st.reads m1 ∧ ∀ c ∈ m1, c ∈ ms := by
      rcases hcf with ⟨-, f, m1, m2, -, h1, -, rfl⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · exact ⟨m1, h1, fun c hc => List.mem_append_left _ hc⟩
      · exact ⟨ms, h, fun c hc => hc⟩
      · exact absurd h hrc
    obtain ⟨m1, h1, hsub⟩ := hm1
    refine readsAgree_of st.reads s (fun v hv => ?_) (fun k e he => ?_) Hfacts
    · obtain ⟨h1, h2, -, -⟩ := Hrevs v hv; omega
    · exact hc _ (hsub _ (readCmpsOk_mem h1 he))
  · rcases hcf with ⟨-, f, m1, m2, hf, -, h2, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · refine ⟨f, hf, fun k hk => writeCmp_holds s _ k ?_⟩
      exact hc _ (List.mem_append_right _ (writeCmpsOk_mem h2 hk))
    · rw [hss] at h; rcases h with h | h <;> exact absurd h (by decide)
    · rw [hss] at h; exact absurd h (by decide)

/-- Choice for a finite family of persistent facts: one witness per index. -/
theorem list_choice {α : Type _} :
    ∀ (n : Nat) (P : Nat → α → IProp GF) (_ : ∀ i a, Persistent (P i a)),
      (□ ∀ i, ⌜i < n⌝ -∗ ∃ a, P i a) ⊢
        ∃ xs : List α, ⌜xs.length = n⌝ ∗ □ ∀ i a, ⌜xs[i]? = some a⌝ -∗ P i a
  | 0, P, _ => by
    iintro #H
    iexists ([] : List α)
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %a %h
    simp at h
  | n + 1, P, hP => by
    iintro #H
    ihave ⟨%a0, #H0⟩ := H $$ %0 %(by omega)
    ihave ⟨%xs, %Hl, #Hxs⟩ := list_choice n (fun i => P (i + 1)) (fun i a => hP (i + 1) a) $$ []
    · imodintro
      iintro %i %hi
      iapply H
      ipureintro; omega
    iexists a0 :: xs
    isplitr
    · ipureintro; simp [Hl]
    imodintro
    iintro %i %a %h
    rcases i with _ | i
    · simp at h; subst h; iexact H0
    · simp at h; iapply Hxs; ipureintro; exact h

/-- **An `Else` get's response is a read** (`rs.add`'s entries): the response of `OpGet(k)` in a
transaction at `r` on `s` (etcd's state at `r`) is the read of `k` at `r`, with its header's
revision. -/
theorem respOp_read (pfx k : GoString) (r : w64) (s : List EtcdKv) (p : Loc) (n : Nat)
    (hwf : EtcdStateWf pfx s) (hk : pfx <+: k) :
    □ etcdState (GF := GF) r pfx s ∗
      txnOpRespAt p (.get (keyOp k)) (.range (rangeSel s (keyOp k)) n) ⊢
      ∃ hr : w64, respOpReadAt pfx k p { hdr := hr, rev := r, kv := kvAt s k } := by
  iintro ⟨#Hs, #Hp⟩
  iunfold txnOpRespAt at Hp
  icases Hp with ⟨%Hpnn, %u, #Hu, %w, %rr, %Huw, #Hw, %Hrrnn, #Hrr⟩
  subst Huw
  iunfold rangeRespAt at Hrr
  icases Hrr with ⟨%ksl, %kps, %kvs, #HK, #Hkps, #Hkv, %Hokv, -, %h, %hr, #HH, %Hhnn, #HR⟩
  have hkvs : kvs = (kvAt s k).toList := by
    obtain ⟨h1, h2⟩ := keyOp_kvs pfx k s kvs hwf Hokv
    cases hk' : kvAt s k with
    | none => exact h1 (kvAt_none hk')
    | some v => exact h2 v (kvAt_some hk').1 (kvAt_some hk').2
  subst hkvs
  iexists hr
  unfold respOpReadAt readRespAt readFact
  isplitr
  · ipureintro; exact Hpnn
  iexists w, rr
  iframe Hu Hw
  isplitr
  · ipureintro; exact Hrrnn
  isplitr
  · iexists s
    iframe Hs
    ipureintro; exact ⟨hwf, rfl, hk⟩
  isplitr
  · iexists h
    iframe HH HR
    ipureintro; exact Hhnn
  · iexists ksl, kps
    iframe HK Hkps Hkv

/-- **The `Else` responses are reads**: the responses `ps` of the gets of `ks` (a failed
transaction at `r` on `s`, etcd's state at `r`) are reads `es` of `ks` at `r`, each of its key's
key-value in `s` (as `rs.add` takes them). -/
theorem elseResps_reads (pfx : GoString) (r : w64) (s : List EtcdKv) (ks : List GoString)
    (ps : List Loc) (hwf : EtcdStateWf pfx s) (hks : ∀ k ∈ ks, pfx <+: k)
    (hlen : ps.length = ks.length) :
    □ etcdState (GF := GF) r pfx s ∗
      (□ ∀ (i : Nat) (p : Loc) (op : TxnOp) (res : TxnOpResult), ⌜ps[i]? = some p⌝ -∗
        ⌜((ks.map keyOp).map TxnOp.get)[i]? = some op⌝ -∗
        ⌜(((ks.map keyOp).map (fun o => TxnOpResult.range (rangeSel s o) (rangeIn s o).length)))[i]?
          = some res⌝ -∗ txnOpRespAt p op res) ⊢
      ∃ es : List ReadM, ⌜es.length = ps.length ∧ ∀ (i : Nat) (e : ReadM), es[i]? = some e →
          ReadM.rev e = r ∧ ∃ k, ks[i]? = some k ∧ ReadM.kv e = kvAt s k⌝ ∗
        □ (∀ (i : Nat) (p : Loc) (k : GoString) (e : ReadM),
          ⌜ps[i]? = some p ∧ ks[i]? = some k ∧ es[i]? = some e⌝ -∗ respOpReadAt pfx k p e) := by
  iintro ⟨#Hs, #Hps⟩
  ihave ⟨%hrs, %Hl, #Hh⟩ := list_choice ps.length (fun i (hr : w64) =>
      iprop(∀ (p : Loc) (k : GoString), ⌜ps[i]? = some p ∧ ks[i]? = some k⌝ -∗
        respOpReadAt (GF := GF) pfx k p { hdr := hr, rev := r, kv := kvAt s k }))
      (fun _ _ => by infer_instance) $$ []
  · imodintro
    iintro %i %hi
    obtain ⟨p, hp⟩ : ∃ p, ps[i]? = some p := ⟨ps[i], List.getElem?_eq_getElem hi⟩
    obtain ⟨k, hk⟩ : ∃ k, ks[i]? = some k :=
      ⟨ks[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hkm : k ∈ ks := List.mem_of_getElem? hk
    ihave Hop := Hps $$ %i %p %(TxnOp.get (keyOp k))
      %(TxnOpResult.range (rangeSel s (keyOp k)) (rangeIn s (keyOp k)).length) %hp
      %(by simp [hk]) %(by simp [hk])
    ihave ⟨%hr, #Hr⟩ := respOp_read pfx k r s p _ hwf (hks k hkm) $$ [Hs Hop]
    · isplitr
      · imodintro; iexact Hs
      · iexact Hop
    iexists hr
    iintro %p' %k' %H
    obtain ⟨hp', hk'⟩ := H
    rw [hp] at hp'; rw [hk] at hk'
    cases hp'; cases hk'
    iexact Hr
  iexists hrs.zipWith (fun hr k => ({ hdr := hr, rev := r, kv := kvAt s k } : ReadM)) ks
  isplitr
  · ipureintro
    refine ⟨by simp [Hl, hlen], fun i e he => ?_⟩
    rw [List.getElem?_zipWith] at he
    cases h1 : hrs[i]? <;> cases h2 : ks[i]? <;> simp [h1, h2] at he
    subst he
    exact ⟨rfl, _, rfl, rfl⟩
  imodintro
  iintro %i %p %k %e %H
  obtain ⟨hp, hk, he⟩ := H
  rw [List.getElem?_zipWith, hk] at he
  cases h1 : hrs[i]? with
  | none => simp [h1] at he
  | some hr =>
    simp [h1] at he
    subst he
    iapply Hh $$ %i %hr %h1 %p %k
    ipureintro; exact ⟨hp, hk⟩

end iprop

end concurrency
end EtcdGrove
end Perennial
