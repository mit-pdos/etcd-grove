/-
#33 S4 (P-raft-3), `notes/antithesis-rawnode-design.md` §2.6, §2.7. **What `RawNode.Ready`'s
strengthened triple reads of the queues**: a queued message's protocol reading (`absMsgOf`) is the
one `outboxRelP` records (`msgAbs`), its destination the message's `To`; so the messages a `Ready`
hands out (`r.msgs` and `msgsAfterAppend`'s to others) read as the outbox's messages to others, and
the self-addressed ones `acceptReady` queues as the outbox's messages to the node, each up to
permutation (`readyMsgs_perm`).
-/
module

public import Proof.go_etcd_io.raft.v3.RawNodeAt
public import Proof.go_etcd_io.raft.v3.LemmasReadyR
public import Proof.go_etcd_io.raft.v3.RawNodeAtLemmas

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- `absMsgOf` is the reading `msgAbs` relates a message to. -/
theorem absMsgOf_of_msgAbs {st : MsgSt} {a : Option Msg} (H : msgAbs st a) : absMsgOf st = a := by
  rcases H with ⟨h, rfl⟩ | ⟨ty, h, hn, rfl⟩ | ⟨sv, h, hs, rfl⟩
  · simp [absMsgOf, h]
  · unfold absMsgOf; rw [h]; cases ty <;> first | rfl | exact absurd rfl hn
  · simp [absMsgOf, h, hs]

/-- A message's reading is addressed to its `To`. -/
theorem absMsgOf_dst {st : MsgSt} {m : Msg} (H : absMsgOf st = some m) : m.dst = st.msg.To' := by
  unfold absMsgOf at H
  split at H
  · cases H
  · obtain ⟨sv, -, rfl⟩ := Option.map_eq_some_iff.1 H; rfl
  · cases H; rfl

/-- The readings of a queue, as `outboxRelP`'s list. -/
theorem filterMap_absMsgOf_eq {ms : List QMsg} {as_ : List (Option Msg)}
    (H : List.Forall₂ (fun q a => msgAbs q.st a) ms as_) :
    ms.filterMap (fun q => absMsgOf q.st) = absList as_ := by
  induction H with
  | nil => rfl
  | @cons q a ms as_ h _ ih =>
    unfold absList at ih ⊢
    rw [List.filterMap_cons, List.filterMap_cons, absMsgOf_of_msgAbs h, ih]
    rfl

/-- (#33 S4, 2026-11-24) A queued message of a type the model describes reads as a protocol message
(a `MsgSnap` carries its snapshot, `msgAbs`). -/
theorem absMsgOf_isSome_of_rel {o : List Msg} {ms1 ms2 : List QMsg} (Ho : outboxRelP o ms1 ms2)
    (q : QMsg) (hq : q ∈ ms1 ++ ms2) (ht : mtypeOf q.st.msg.Type' ≠ none) :
    (absMsgOf q.st).isSome := by
  obtain ⟨as1, as2, -, F1, F2⟩ := Ho
  have key : ∀ {ms : List QMsg} {as_ : List (Option Msg)},
      List.Forall₂ (fun q a => msgAbs q.st a) ms as_ →
      ∀ q ∈ ms, mtypeOf q.st.msg.Type' ≠ none → (absMsgOf q.st).isSome := by
    intro ms as_ H
    induction H with
    | nil => intro q hq; cases hq
    | @cons q' a ms as_ h _ ih =>
      intro q hq ht
      rcases List.mem_cons.1 hq with rfl | hq
      · rw [absMsgOf_of_msgAbs h]
        rcases h with ⟨h1, -⟩ | ⟨_, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
        · exact absurd h1 ht
        · rfl
        · rfl
      · exact ih q hq ht
  rcases List.mem_append.1 hq with h | h
  · exact key F1 q h ht
  · exact key F2 q h ht

/-- Filtering the readings by destination is filtering the queue by `To`. -/
theorem filter_filterMap_absMsgOf (p : w64 → Bool) (l : List QMsg) :
    (l.filterMap (fun q => absMsgOf q.st)).filter (fun m => p m.dst) =
      (l.filter (fun q => p q.st.msg.To')).filterMap (fun q => absMsgOf q.st) := by
  rw [List.filter_filterMap, List.filterMap_filter]
  congr 1
  funext q
  cases h : absMsgOf q.st with
  | none => simp
  | some m =>
    have hd := absMsgOf_dst h
    simp only [Option.filter_some, hd]

/-- **The `Ready`'s messages and the queue `acceptReady` builds, against the outbox**: with the
outbox the two queues' readings (`outboxRelP`) and `r.msgs` to others (`QOk`), the messages handed
out (`r.msgs`, then `msgsAfterAppend`'s to others) read as the outbox's to others, and
`msgsAfterAppend`'s to the node as the outbox's to the node. -/
theorem readyMsgs_perm (id : w64) (o : List Msg) (ms1 ms2 : List QMsg) (Ho : outboxRelP o ms1 ms2)
    (H1 : ∀ q ∈ ms1, q.st.msg.To' ≠ id) :
    (ms1 ++ nonself id ms2).filterMap (fun q => absMsgOf q.st) ≡ₚ
        o.filter (fun m => decide (m.dst ≠ id)) ∧
      (selfmsgs id ms2).filterMap (fun q => absMsgOf q.st) ≡ₚ
        o.filter (fun m => decide (m.dst = id)) := by
  obtain ⟨as1, as2, Hp, F1, F2⟩ := Ho
  have Hall : o ≡ₚ (ms1 ++ ms2).filterMap (fun q => absMsgOf q.st) := by
    rw [List.filterMap_append, filterMap_absMsgOf_eq F1, filterMap_absMsgOf_eq F2]; exact Hp
  have H1' : ms1.filter (fun q => decide (q.st.msg.To' ≠ id)) = ms1 :=
    List.filter_eq_self.2 (fun q hq => decide_eq_true (H1 q hq))
  have H1'' : ms1.filter (fun q => decide (q.st.msg.To' = id)) = [] :=
    List.filter_eq_nil_iff.2 (fun q hq => by simpa using H1 q hq)
  refine ⟨?_, ?_⟩
  · have := (Hall.filter (fun m => decide (m.dst ≠ id))).symm
    rw [filter_filterMap_absMsgOf (fun t => decide (t ≠ id)), List.filter_append, H1'] at this
    refine List.Perm.trans ?_ this
    unfold nonself isSelfQ
    have e : ms2.filter (fun q => !decide (q.st.msg.To' = id)) =
        ms2.filter (fun q => decide (q.st.msg.To' ≠ id)) := by
      apply List.filter_congr; intro q _; simp
    rw [e]
  · have := (Hall.filter (fun m => decide (m.dst = id))).symm
    rw [filter_filterMap_absMsgOf (fun t => decide (t = id)), List.filter_append, H1'',
      List.nil_append] at this
    exact this

/-- **The entries a `Ready` hands out, against the log** (the log's boundary at index `0`): the
first one is at the in-progress boundary, and they are the log's from it on. -/
theorem nextUnstable_head (ls : LogState) (Hidx : LogIndicesOk ls.prev (ls.sents ++ ls.uents))
    (Hb : logOffset ls ≤ uint.Z ls.inprogress) (Hp0 : uint.Z ls.prev.index' = 0) :
    ∀ e0 ∈ (nextUnstable ls).head?,
      (ls.sents ++ ls.uents).drop (uint.nat e0.Index' - 1) = nextUnstable ls ∧
      uint.nat e0.Index' = uint.nat ls.inprogress := by
  intro e0 he
  unfold logOffset at Hb
  unfold nextUnstable logOffset at he ⊢
  generalize hk : (uint.Z ls.inprogress - (uint.Z ls.prev.index' + ↑ls.sents.length + 1)).toNat = k
    at he ⊢
  rw [List.head?_drop] at he
  have he' : (ls.sents ++ ls.uents)[ls.sents.length + k]? = some e0 := by
    rw [List.getElem?_append_right (by omega)]; simpa using he
  have Hi := Hidx _ _ he'
  have hn1 : (uint.nat e0.Index' : Int) = uint.Z e0.Index' := rfl
  have hn2 : (uint.nat ls.inprogress : Int) = uint.Z ls.inprogress := rfl
  push_cast at Hi
  have Hix : uint.nat e0.Index' = ls.sents.length + k + 1 := by omega
  refine ⟨?_, by omega⟩
  rw [Hix, show ls.sents.length + k + 1 - 1 = ls.sents.length + k by omega]
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    Nat.add_sub_cancel_left]

/-- `PendAbs` of two queues one after the other. -/
theorem PendAbs.append {a c : List MsgSt} {b d : List Pending} {q1 q2 : List Msg}
    (H1 : PendAbs a b q1) (H2 : PendAbs c d q2) : PendAbs (a ++ c) (b ++ d) (q1 ++ q2) := by
  obtain ⟨l1, e1⟩ := H1
  obtain ⟨l2, e2⟩ := H2
  refine ⟨by simp [l1, l2], ?_⟩
  rw [List.zip_append l1, List.filterMap_append, ← e1, ← e2]

/-- A queue of self-addressed responses (`selfPending`) reads as its messages. -/
theorem PendAbs.selfs (sm : List QMsg) :
    PendAbs (sm.map QMsg.st) (sm.map (fun q => selfPending q.st.msg))
      (sm.filterMap (fun q => absMsgOf q.st)) := by
  induction sm with
  | nil => exact ⟨rfl, rfl⟩
  | cons q sm ih =>
    have H1 : PendAbs [q.st] [selfPending q.st.msg] (absMsgOf q.st).toList := by
      refine ⟨rfl, ?_⟩
      cases h : absMsgOf q.st <;> simp [selfPending, h]
    have e : (q :: sm).filterMap (fun q => absMsgOf q.st) =
        (absMsgOf q.st).toList ++ sm.filterMap (fun q => absMsgOf q.st) := by
      cases h : absMsgOf q.st <;> simp [List.filterMap_cons, h]
    rw [List.map_cons, List.map_cons, e]
    exact PendAbs.append H1 ih

/-- A queue of acknowledgements (no `Pending.self`) reads as nothing. -/
theorem PendAbs.acks (sts : List MsgSt) (aps : List Pending) (Hl : sts.length = aps.length)
    (Haps : ∀ p ∈ aps, ∀ pv t, p ≠ .self pv t) : PendAbs sts aps [] := by
  refine ⟨Hl, ?_⟩
  symm
  apply List.filterMap_eq_nil_iff.2
  intro x hx
  have hp := Haps x.2 (List.of_mem_zip hx).2
  obtain ⟨a, b⟩ := x
  cases b with
  | self pv t => exact absurd rfl (hp pv t)
  | _ => rfl

end pure

section sep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The queue `acceptReady` builds, at its messages' states** (`pendAt` with no loan): the
self-addressed responses at their own states (`self_pending`), then the acknowledgements, which
carry no protocol message; its protocol messages are the responses' readings. -/
theorem pendAt_ready (γ : RaftNames) (id : w64) (W : DurMaps) (sm : List QMsg) (acks : List Loc)
    (aps : List Pending) (Haps : ∀ p ∈ aps, ∀ pv t, p ≠ .self pv t) :
    ([∗list] l;x ∈ sm.map QMsg.loc; (sm.map QMsg.st).zip (sm.map (fun q => selfPending q.st.msg)),
        msgIn (GF := GF) l DFrac.discard x.1 ∗ pendingRel γ id W x.1 x.2) ⊢
      pendList γ id W acks aps -∗
      pendAt γ id W none (sm.map QMsg.loc ++ acks) (sm.map (fun q => selfPending q.st.msg) ++ aps)
        (sm.filterMap (fun q => absMsgOf q.st)) := by
  iintro Hs Ha
  icases pendList_named γ id W acks aps $$ Ha with ⟨%sts, %Hl, Ha⟩
  simp only [pendAt]
  iexists (sm.map QMsg.st ++ sts)
  have Hz : ((sm.map QMsg.st) ++ sts).zip (sm.map (fun q => selfPending q.st.msg) ++ aps) =
      (sm.map QMsg.st).zip (sm.map (fun q => selfPending q.st.msg)) ++ sts.zip aps :=
    List.zip_append (by simp)
  isplitr
  · ipureintro
    have H := PendAbs.append (PendAbs.selfs sm) (PendAbs.acks sts aps Hl Haps)
    rw [List.append_nil] at H
    exact H
  · rw [Hz]
    iapply (BigSepL2.bigSepL2_app_wand (Φ := fun _ (l : Loc) (x : MsgSt × Pending) =>
      iprop(msgIn (GF := GF) l DFrac.discard x.1 ∗ pendingRel γ id W x.1 x.2))) $$ Hs Ha

/-- A `Ready`'s soft state at a `nil` pointer is none (`softStateIs`'s `some` arm: not `nil`). -/
theorem softStateIs_null (p : Loc) (ss : Option (w64 × StateType)) :
    softStateIs (GF := GF) p ss ⊢ ⌜p = null → ss = none⌝ := by
  rcases ss with _ | ⟨l, r⟩
  · iintro -; ipureintro; intro _; rfl
  · unfold softStateIs; iintro ⟨%Hn, -⟩; ipureintro; intro h; exact absurd h Hn

/-- (antithesis parity B1) `KTie` across a step that keeps the flags and the node constant. -/
theorem KTie.keep {rs rs' : RNState} {s s' : NState} (H : KTie rs s)
    (hfl : s'.prevote = s.prevote ∧ s'.cq = s.cq ∧ s'.sdr = s.sdr) (hk : rs'.k = rs.k) :
    KTie rs' s' := by
  unfold KTie at *; rw [hk, ← H, hfl.1, hfl.2.1, hfl.2.2]

/-- The scope kept, at every mode, by a step that keeps what it reads (`RnScope md`), the storage,
the `Config` flags and the node constant. -/
theorem rnScopeAt_keepAll {γ : RaftNames} {id : w64} (sc : Option RnMode) (rs rs' : RNState)
    (s s' : NState) (H : ∀ md, RnScope md id rs s → RnScope md id rs' s')
    (Hst : s'.logst.storage = s.logst.storage)
    (hcf : rs'.mode = rs.mode ∧ rs'.cfg = rs.cfg := by exact ⟨rfl, rfl⟩)
    (hfl : s'.prevote = s.prevote ∧ s'.cq = s.cq ∧ s'.sdr = s.sdr := by exact ⟨rfl, rfl, rfl⟩)
    (hk : rs'.k = rs.k := by rfl)
    (hx : (toPState s').lead = (toPState s).lead ∧ s'.gh.xw = s.gh.xw ∧ s'.term = s.term := by
      exact ⟨rfl, rfl, rfl⟩) :
    rnScopeAt (GF := GF) γ id sc rs s ⊢ rnScopeAt γ id sc rs' s' := by
  cases sc with
  | none => unfold rnScopeAt; iintro _; iempintro
  | some md =>
    unfold rnScopeAt
    iintro ⟨%Hs, #Hc⟩
    rw [Hst]
    isplitr
    · ipureintro
      exact ⟨H md Hs.1, RnCfgIn.keep hcf Hs.2.1, Hs.2.2.1.keep hfl hk, fun h => (Hs.2.2.2 h).keep hx⟩
    · imodintro; iexact Hc

/-- The scope at one mode `md` kept by a step that keeps `RnScope md` (an input whose effect grows what
another mode excludes: a read request at reads on), the storage, the `Config` flags and the node
constant. -/
theorem rnScopeAt_keepSome {γ : RaftNames} {id : w64} (md : RnMode) (rs rs' : RNState)
    (s s' : NState) (H : RnScope md id rs s → RnScope md id rs' s')
    (Hst : s'.logst.storage = s.logst.storage)
    (hcf : rs'.mode = rs.mode ∧ rs'.cfg = rs.cfg := by exact ⟨rfl, rfl⟩)
    (hfl : s'.prevote = s.prevote ∧ s'.cq = s.cq ∧ s'.sdr = s.sdr := by exact ⟨rfl, rfl, rfl⟩)
    (hk : rs'.k = rs.k := by rfl)
    (hx : (toPState s').lead = (toPState s).lead ∧ s'.gh.xw = s.gh.xw ∧ s'.term = s.term := by
      exact ⟨rfl, rfl, rfl⟩) :
    rnScopeAt (GF := GF) γ id (some md) rs s ⊢ rnScopeAt γ id (some md) rs' s' := by
  unfold rnScopeAt
  iintro ⟨%Hs, #Hc⟩
  rw [Hst]
  isplitr
  · ipureintro
    exact ⟨H Hs.1, RnCfgIn.keep hcf Hs.2.1, Hs.2.2.1.keep hfl hk, fun h => (Hs.2.2.2 h).keep hx⟩
  · imodintro; iexact Hc

/-- `rnScopeAt_keepSome` for a step that may change the transfer facts' inputs (a transfer request:
the ghost records `xw` grow), given `XScopeOk` across it. -/
theorem rnScopeAt_keepSomeX {γ : RaftNames} {id : w64} (md : RnMode) (rs rs' : RNState)
    (s s' : NState) (H : RnScope md id rs s → RnScope md id rs' s')
    (Hst : s'.logst.storage = s.logst.storage)
    (hcf : rs'.mode = rs.mode ∧ rs'.cfg = rs.cfg := by exact ⟨rfl, rfl⟩)
    (hfl : s'.prevote = s.prevote ∧ s'.cq = s.cq ∧ s'.sdr = s.sdr := by exact ⟨rfl, rfl, rfl⟩)
    (hk : rs'.k = rs.k := by rfl)
    (hx : md.transfer = true → XScopeOk γ s → XScopeOk γ s') :
    rnScopeAt (GF := GF) γ id (some md) rs s ⊢ rnScopeAt γ id (some md) rs' s' := by
  unfold rnScopeAt
  iintro ⟨%Hs, #Hc⟩
  rw [Hst]
  isplitr
  · ipureintro
    exact ⟨H Hs.1, RnCfgIn.keep hcf Hs.2.1, Hs.2.2.1.keep hfl hk, fun h => hx h (Hs.2.2.2 h)⟩
  · imodintro; iexact Hc

/-- (antithesis parity B1, step C) **The scope at an option, read out**: at every mode it names, its pure
part. -/
theorem rnScopeAt_pureOpt {γ : RaftNames} {id : w64} (sc : Option RnMode) (rs : RNState) (s : NState) :
    rnScopeAt (GF := GF) γ id sc rs s ⊢
      ⌜∀ md, sc = some md → RnScope md id rs s ∧ RnCfgIn md γ id rs ∧ KTie rs s ∧
        (md.transfer = true → XScopeOk γ s)⌝ ∗ rnScopeAt γ id sc rs s := by
  cases sc with
  | none => iintro H; iframe H; ipureintro; intro md h; cases h
  | some md0 =>
    unfold rnScopeAt
    iintro ⟨%H, #Hc⟩
    isplitr
    · ipureintro; intro md h; cases h; exact H
    · isplitr
      · ipureintro; exact H
      · imodintro; iexact Hc

/-- The storage never compacted past `0`, at a mode without snapshots. -/
theorem rnScopeAt_capOpt {γ : RaftNames} {id : w64} {sc : Option RnMode} {md : RnMode} (h : sc = some md)
    (hs : md.snapshots = false) (rs : RNState) (s : NState) :
    rnScopeAt (GF := GF) γ id sc rs s ⊢ storCapF s.logst.storage 0 ∗ rnScopeAt γ id sc rs s := by
  subst h
  unfold rnScopeAt
  iintro ⟨%H, #Hc⟩
  isplitr
  · iapply Hc; ipureintro; exact hs
  · isplitr
    · ipureintro; exact H
    · imodintro; iexact Hc

/-- `rnScopeAt_keepSomeX` at an option: at each mode it names, `RnScope` kept and the transfer facts. -/
theorem rnScopeAt_keepOpt {γ : RaftNames} {id : w64} (sc : Option RnMode) (rs rs' : RNState)
    (s s' : NState) (H : ∀ md, sc = some md → RnScope md id rs s → RnScope md id rs' s')
    (Hst : s'.logst.storage = s.logst.storage)
    (hcf : rs'.mode = rs.mode ∧ rs'.cfg = rs.cfg := by exact ⟨rfl, rfl⟩)
    (hfl : s'.prevote = s.prevote ∧ s'.cq = s.cq ∧ s'.sdr = s.sdr := by exact ⟨rfl, rfl, rfl⟩)
    (hk : rs'.k = rs.k := by rfl)
    (hx : ∀ md, sc = some md → md.transfer = true → XScopeOk γ s → XScopeOk γ s') :
    rnScopeAt (GF := GF) γ id sc rs s ⊢ rnScopeAt γ id sc rs' s' := by
  cases sc with
  | none => unfold rnScopeAt; iintro _; iempintro
  | some md =>
    exact rnScopeAt_keepSomeX md rs rs' s s' (H md rfl) Hst hcf hfl hk (hx md rfl)

/-- The basic scope kept by a step that keeps what it reads (`RnScopeBasic`), the storage, the
`Config` flags and the node constant. -/
theorem rnScopeAt_keep {γ : RaftNames} {id : w64} (sc : Bool) (rs rs' : RNState) (s s' : NState)
    (H : RnScopeBasic rs s → RnScopeBasic rs' s') (Hst : s'.logst.storage = s.logst.storage)
    (hcf : rs'.mode = rs.mode ∧ rs'.cfg = rs.cfg := by exact ⟨rfl, rfl⟩)
    (hfl : s'.prevote = s.prevote ∧ s'.cq = s.cq ∧ s'.sdr = s.sdr := by exact ⟨rfl, rfl, rfl⟩)
    (hk : rs'.k = rs.k := by rfl) :
    rnScopeAt (GF := GF) γ id (basicScope sc) rs s ⊢ rnScopeAt γ id (basicScope sc) rs' s' := by
  cases sc with
  | false =>
    unfold rnScopeAt basicScope; iintro _; iempintro
  | true =>
    unfold rnScopeAt basicScope
    iintro ⟨%Hs, #Hc⟩
    rw [Hst]
    isplitr
    · ipureintro
      exact ⟨(RnScope_empty rs' s').2 (H ((RnScope_empty rs s).1 Hs.1)), RnCfgIn.keep hcf Hs.2.1,
        Hs.2.2.1.keep hfl hk, fun h => absurd h (by decide)⟩
    · imodintro; iexact Hc

end sep

end EtcdGrove
end Perennial
