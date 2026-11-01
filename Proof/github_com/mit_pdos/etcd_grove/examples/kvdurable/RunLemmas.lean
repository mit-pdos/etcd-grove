/-
Lean-first (no Rocq counterpart).

# What kvdurable's `run` uses beside the methods' specs (2026-11-01, stage II (j))

kvreconf's `RunApply`, `RunSnap` and `RunAppend` lemmas at kvdurable's predicates (kvreconf's carry
its package assumption as a section variable): the `Ready`'s read states (`kd_readStatesPts_rsOk`),
the applier's view carried and opened (`appNode_extend`, `appNode_open`, `appNode_snap`), a snapshot
handed out by the node (`kd_snap_recv`), the `Append` lent ranges (`append_none_pre/post`,
`snapAppend_pre/post`) and `Advance`'s receipts (`kd_snapReceipt`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunBatch

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section run
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

instance kdSnapRecOk_timeless (γr : KdNames) (s : SnapRec) :
    Timeless (kdSnapRecOk (GF := GF) γr s) := by
  unfold kdSnapRecOk; infer_instance

/-- The `ReadState` values of a `Ready`'s read states, each `rsOk`. -/
theorem kd_rsOk_of_readStates (γ : Cluster) :
    ∀ (vs : List ReadState) (sts : List ReadStateM),
    ([∗list] v;st ∈ vs;sts, ⌜v.Index' = st.Index'⌝ ∗ v.RequestCtx' ↦*□ st.RequestCtx') ∗
      ([∗list] st ∈ sts, readStateOk (GF := GF) γ kdRaftN st.RequestCtx' st.Index') ⊢
      [∗list] v ∈ vs, rsOk γ v
  | [], _ => by
    iintro ⟨-, -⟩
    iapply (BigSepL.bigSepL_nil (Φ := fun _ v => rsOk (GF := GF) γ v)).2; iempintro
  | v :: vs, [] => by
    iintro ⟨Hb, -⟩
    ihave %Hl := BigSepL2.bigSepL2_length $$ Hb
    simp at Hl
  | v :: vs, st :: sts => by
    iintro ⟨Hb, #Hok⟩
    icases (BigSepL2.bigSepL2_cons).1 $$ Hb with ⟨⟨%Hi, #Hc⟩, #Hb'⟩
    icases (BigSepL.bigSepL_cons).1 $$ Hok with ⟨#Hok1, #Hok'⟩
    iapply (BigSepL.bigSepL_cons (Φ := fun _ v => rsOk (GF := GF) γ v)).2
    isplitl []
    · unfold rsOk
      iexists st.RequestCtx'
      iframe Hc
      rw [Hi]
      iexact Hok1
    · ihave H := kd_rsOk_of_readStates γ vs sts $$ [Hb' Hok']
      · iframe Hb' Hok'
      iexact H

/-- The `ReadState` values a `Ready` hands out, each `rsOk`. -/
theorem kd_readStatesPts_rsOk (γ : Cluster) (rs : GoSlice) (sts : List ReadStateM) :
    readStatesPts (GF := GF) rs sts ∗
      ([∗list] st ∈ sts, readStateOk γ kdRaftN st.RequestCtx' st.Index') ⊢
      ∃ vs : List ReadState, rs ↦*□ vs ∗ [∗list] v ∈ vs, rsOk γ v := by
  iintro ⟨H, #Hok⟩
  iunfold readStatesPts at H
  icases H with ⟨%vs, #Hs, #Hb⟩
  iexists vs
  iframe Hs
  ihave H := kd_rsOk_of_readStates γ vs sts $$ [Hb Hok]
  · iframe Hb Hok
  iexact H

/-- `skippedIn` reads the entries below its end only: it carries to a longer log. -/
theorem kd_skippedIn_prefix (γ : Cluster) (l l' : List LogEntry) (a b : Nat) (hp : l <+: l')
    (hb : b ≤ l.length) :
    skippedIn (GF := GF) γ l a b ⊢ skippedIn γ l' a b := by
  unfold skippedIn
  apply BigSepL.bigSepL_mono
  intro k j hj
  have hm := List.mem_range'_1.1 (List.mem_of_getElem? hj)
  have hjl : j < l.length := by omega
  obtain ⟨t, rfl⟩ := hp
  have hget : (l ++ t)[j]? = l[j]? := List.getElem?_append_left hjl
  iintro #H %e %he
  iapply H
  ipureintro
  rw [← hget]; exact he

/-- The applier's view carried to a longer delivered log. -/
theorem appNode_extend (γr : KdNames) (n : Loc) (l l' : List LogEntry) (k : Nat) (m : Membership)
    (hp : l <+: l') (hk : k ≤ l.length) :
    appNode (GF := GF) γr n l k m ∗ deliveredLogLb n γr.r.cluster kdRaftN l' ⊢ appNode γr n l' k m := by
  unfold appNode
  iintro ⟨⟨%v, Hc, -, #Hs, %Hv⟩, #Hd⟩
  iexists v
  iframe Hc Hd
  isplitl []
  · iapply kd_skippedIn_prefix _ l l' _ _ hp hk $$ Hs
  ipureintro; exact Hv

/-- The applier's view opened for `Advance`: the node's configuration view, every conf entry
from its index skipped. -/
theorem appNode_open (γr : KdNames) (n : Loc) (l : List LogEntry) (k : Nat) (m : Membership) :
    appNode (GF := GF) γr n l k m ⊢ ∃ v : ConfigView, nodeConfig n γr.r.cluster kdRaftN v ∗
      skippedIn γr.r.cluster l v.applied k ∗
      (nodeConfig n γr.r.cluster kdRaftN v -∗ appNode γr n l k m) := by
  unfold appNode
  iintro ⟨%v, Hc, #Hd, #Hs, %Hv⟩
  iexists v
  iframe Hc Hs
  iintro Hc
  iexists v
  iframe Hc Hd Hs
  ipureintro; exact Hv

/-- A delivered log with an entry frozen above the compaction point is shorter than `2^61`. -/
theorem kd_frozenTo_len (γs : MemStorNames) (c : Nat) (D : List LogEntry) :
    kvreconf.frozenTo (GF := GF) γs c D ⊢ ⌜c < D.length → D.length < 2 ^ 61⌝ := by
  unfold kvreconf.frozenTo
  iintro #H
  ihave %Hb := memLog_bound _ _ _ _ $$ H
  ipureintro
  intro hc
  rw [List.length_drop, kvreconf.kvr_toEntries_length] at Hb
  rcases Hb with h | h
  · have := congrArg List.length h
    rw [List.length_drop, kvreconf.kvr_toEntries_length] at this
    simp at this; omega
  · omega

/-- Two committed logs of the same length are the same. -/
theorem kd_committed_eq (γ : Cluster) (l1 l2 : List LogEntry) (h : l1.length = l2.length) :
    isCommittedLogLb (GF := GF) γ l1 ∗ isCommittedLogLb γ l2 ⊢ ⌜l1 = l2⌝ := by
  iintro ⟨#H1, #H2⟩
  ihave %Hag := isCommittedLogLb_agree γ l1 l2 $$ [H1 H2]
  · iframe H1 H2
  ipureintro
  rcases Hag with hp | hp
  · exact hp.eq_of_length h
  · exact (hp.eq_of_length h.symm).symm

/-- **A snapshot handed out by the node** (see the file header), at the committed log `L` of its
index. -/
theorem kd_snap_recv (γr : KdNames) (vs : List w64) (sv : SnapshotM) (L : List LogEntry)
    (Hpos : 0 < uint.Z sv.Metadata'.Index') (Hi : uint.Z sv.Metadata'.Index' < 2 ^ 61)
    (Hlen : L.length = uint.nat sv.Metadata'.Index') :
    ⊢ kdCluster (GF := GF) γr vs -∗ isCommittedLogLb γr.r.cluster L -∗
      snapshotCert γr.r.cluster kdRaftN (snapTrip sv sv.Metadata'.ConfState'.lists) ={⊤}=∗
      snapshotValid γr.r.cluster sv ∗ ∃ m : Membership, confAt γr.r.cluster L.length m ∗
        ⌜confStateIs sv.Metadata'.ConfState' m ∧ GMap.size m.ids < 2 ^ 61 ∧ kvreconf.kvSnapOk L sv.Data'⌝ := by
  iintro #Hcl #HL #Hcert
  unfold kdCluster
  icases Hcl with ⟨#Hc, -, -, #Hinv, -, -⟩
  ihave #Hsv := snapshotCert_valid γr.r.cluster kdRaftN sv Hpos Hi $$ [Hc Hcert]
  · iframe Hc Hcert
  ihave #Hsv' := Hsv
  unfold snapshotValid
  icases Hsv' with ⟨%l1, %m1, #Hl1, #Hca1, #Hmade, %Hp⟩
  ihave %Heq := kd_committed_eq γr.r.cluster l1 L (by rw [Hlen]; exact Hp.1) $$ [Hl1 HL]
  · iframe Hl1 HL
  subst Heq
  unfold kdSnapInv
  iinv Hinv with Hb Hclose
  icases Hb with ⟨%S, >Hown, >#HS⟩
  ihave ⟨⟨Hown, -⟩, %Hin⟩ := persistent_entails_left (snapMade_elem γr.r.cluster S _) $$ [Hown Hmade]
  · iframe Hown Hmade
  ihave #Hrec := BigSepL.bigSepL_mem (Φ := fun s => kdSnapRecOk (GF := GF) γr s) Hin $$ HS
  imod Hclose $$ [Hown] with -
  · inext
    iexists S
    iframe Hown HS
  imodintro
  iframe Hsv
  iexists m1
  iframe Hca1
  unfold kdSnapRecOk
  icases Hrec with ⟨%L2, #HL2, -, %Hr⟩
  simp only at Hr
  ihave %Heq := kd_committed_eq γr.r.cluster L2 l1 Hr.1 $$ [HL2 Hl1]
  · iframe HL2 Hl1
  subst Heq
  ipureintro
  exact ⟨Hp.2.2.2.1, Hr.2.2, Hr.2.1⟩

/-- Before `Append` after a snapshot: the range lent to it (empty, after the dummy), and what is
kept. -/
theorem snapAppend_pre (γs : MemStorNames) (j : Nat) (es : List EntryM) :
    memEnd (GF := GF) γs j ⊢
      (if es = [] then emp else memLog γs j (DFrac.own 1) [] ∗ memEnd γs (j + ([] : List EntryM).length)) ∗
      (if es = [] then memEnd γs j else emp) := by
  iintro He
  by_cases h : es = []
  · simp only [h, ↓reduceIte]
    iframe He
  · simp only [h, ↓reduceIte, List.length_nil, Nat.add_zero]
    iframe He
    iapply memLog_nil

/-- After `Append` after a snapshot: the batch's range, owned, and the storage's end after it. -/
theorem snapAppend_post (γs : MemStorNames) (j : Nat) (es : List EntryM) :
    (if es = [] then emp else memLog (GF := GF) γs j (DFrac.own 1) es ∗ memEnd γs (j + es.length)) ∗
      (if es = [] then memEnd γs j else emp) ⊢
      memLog γs j (DFrac.own 1) es ∗ memEnd γs (j + es.length) := by
  by_cases h : es = []
  · subst h
    simp only [↓reduceIte, List.length_nil, Nat.add_zero]
    iintro ⟨-, He⟩
    iframe He
    iapply memLog_nil
  · simp only [h, ↓reduceIte]
    iintro ⟨⟨Hl, He⟩, -⟩
    iframe Hl He

/-- **`Advance`'s receipt for a snapshot loan**, at the wrapper's interface. -/
theorem kd_snapReceipt (st ms : Loc) (γs : MemStorNames) (l : SnapLoan) (es : List EntryM) :
    ⊢ kdStorRec (GF := GF) st ms γs -∗ ownSnapM l.ptr (DFrac.own (Qp.half 1)) l.snap -∗
      memCompacted γs (uint.nat l.snap.Metadata'.Index') -∗
      memLog γs (uint.nat l.snap.Metadata'.Index') DFrac.discard [memDummy l.snap] -∗
      memLog γs (uint.nat l.snap.Metadata'.Index' + 1) (DFrac.own 1) es -∗
      memEnd γs (uint.nat l.snap.Metadata'.Index' + 1 + es.length) -∗
      snapReceipt (kdStorIface st) l es := by
  iintro #Hrec Hs #Hc #Hd Hl He
  unfold snapReceipt
  iframe Hs
  isplitl []
  · iapply kdStorCompacted_of st ms γs _ $$ Hrec Hc
  isplitl []
  · iexists memDummy l.snap
    isplitr
    · ipureintro; rfl
    iapply kdStorLog_of st ms γs _ _ _ $$ Hrec Hd
  ihave Hl := kdStorLog_of st ms γs _ _ _ $$ Hrec Hl
  ihave He := kdStorEnd_of st ms γs _ $$ Hrec He
  iframe Hl He

/-- The applier's view after a snapshot `Ready`'s `Advance`: at the snapshot's index, the end of
the delivered log. -/
theorem appNode_snap (γr : KdNames) (n : Loc) (L : List LogEntry) (i : Nat) (m : Membership)
    (h : L.length = i) :
    nodeConfig (GF := GF) n γr.r.cluster kdRaftN ⟨i, m⟩ ∗ deliveredLogLb n γr.r.cluster kdRaftN L ⊢
      appNode γr n L L.length m := by
  iintro ⟨Hc, #Hd⟩
  unfold appNode
  iexists ⟨i, m⟩
  iframe Hc Hd
  isplitl []
  · iapply skippedIn_noConf
    intro j e h1 h2; simp only at h1 h2; omega
  · ipureintro; exact ⟨rfl, by simp only; omega⟩

/-- Nothing above the end of the delivered log is frozen. -/
theorem kd_frozenTo_snap (γs : MemStorNames) (L : List LogEntry) (c : Nat) (h : L.length = c) :
    ⊢ kvreconf.frozenTo (GF := GF) γs c L := by
  unfold kvreconf.frozenTo
  rw [List.drop_eq_nil_of_le (by rw [kvreconf.kvr_toEntries_length]; omega)]
  iapply memLog_nil

theorem append_none_pre (st ms : Loc) (γs : MemStorNames) (es : List EntryM) :
    ⊢ kdStorRec (GF := GF) st ms γs -∗ appendRight (kdStorIface st) es -∗
      ∃ (k : Nat) (old : List EntryM),
        ⌜(∀ e0, es.head? = some e0 → k = uint.nat e0.Index') ∧ (es = [] → k = 0)⌝ ∗
        (if es = [] then emp else memLog γs k (DFrac.own 1) old ∗ memEnd γs (k + old.length)) := by
  iintro #Hrec Happ
  iunfold appendRight at Happ
  icases Happ with (%He | ⟨%e0, %old, %Hh, Hl, He⟩)
  · subst He
    iexists 0, []
    simp only [if_true]
    isplitr
    · ipureintro; simp
    itrivial
  · iexists uint.nat e0.Index', old
    have hne : es ≠ [] := by intro h; subst h; cases Hh
    simp only [if_neg hne]
    isplitr
    · ipureintro; exact ⟨fun e h => by rw [Hh] at h; cases h; rfl, fun h => absurd h hne⟩
    ihave Hl := kdStorLog_to st ms γs _ _ _ $$ Hrec Hl
    ihave He := kdStorEnd_to st ms γs _ $$ Hrec He
    iframe Hl He

theorem append_none_post (st ms : Loc) (γs : MemStorNames) (c : Nat) (D ce : List LogEntry)
    (es : List EntryM) (k : Nat) (Hc : c ≤ D.length)
    (Hin : ∀ e0, es.head? = some e0 → ∀ (j : Nat) (e : LogEntry), ce[j]? = some e →
      uint.nat e0.Index' ≤ D.length + 1 + j →
      Option.map LogEntry.ofEntryM es[D.length + 1 + j - uint.nat e0.Index']? = some e)
    (Hidx : ∀ e0, es.head? = some e0 → ∀ j e, es[j]? = some e →
      uint.nat e.Index' = uint.nat e0.Index' + j)
    (Hk : ∀ e0, es.head? = some e0 → k = uint.nat e0.Index') :
    ⊢ kdStorRec (GF := GF) st ms γs -∗ kvreconf.frozenTo γs c D -∗
      ceFrozen (kdStorIface st) D.length (LogEntry.toEntries ce D.length) es -∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length)) ==∗
      kvreconf.frozenTo γs c (D ++ ce) ∗ advReceipt (kdStorIface st) (D ++ ce).length es none := by
  iintro #Hrec #Hf #Hcf Hb
  iunfold ceFrozen at Hcf
  icases Hcf with ⟨%m0, #Hm0, %Hm⟩
  ihave #Hm0 := kdStorLog_to st ms γs _ _ _ $$ Hrec Hm0
  have Hm' : m0 = ce.length ∨ ∃ e0, es.head? = some e0 ∧ D.length + 1 + m0 = uint.nat e0.Index' := by
    rw [kvreconf.kvr_toEntries_length] at Hm; exact Hm
  imod kvreconf.batch_freeze γs c D ce es m0 k Hc Hm' Hin Hidx Hk $$ Hf Hm0 Hb with ⟨#Hf', %a, %Ha, Hr⟩
  imodintro
  iframe Hf'
  unfold advReceipt
  iexists a
  isplitl
  · unfold appendReceipt
    by_cases he : es = []
    · ileft; ipureintro; exact he
    · iright
      simp only [if_neg he]
      icases Hr with ⟨#Ha', Hb', He'⟩
      obtain ⟨e0, he0⟩ : ∃ e0, es.head? = some e0 := by
        cases es with
        | nil => exact absurd rfl he
        | cons x xs => exact ⟨x, rfl⟩
      iexists e0, es.drop a.length
      isplitr
      · ipureintro
        obtain ⟨t, rfl⟩ := Ha.2
        refine ⟨he0, ?_⟩
        simp
      rw [← Hk e0 he0]
      ihave Ha' := kdStorLog_of st ms γs _ _ _ $$ Hrec Ha'
      ihave Hb' := kdStorLog_of st ms γs _ _ _ $$ Hrec Hb'
      ihave He' := kdStorEnd_of st ms γs _ $$ Hrec He'
      iframe Ha' Hb' He'
  · ipureintro
    intro hne e0 he0
    have := Ha.1 hne
    rw [Hk e0 he0] at this
    exact this

/-- **A `Ready`'s messages with their `sentMsg`** (kvreconf's `readyMsgs_sent`). -/
theorem kd_readyMsgs_sent (γ : Cluster) (N : Namespace) (id : w64) (ms : List QMsg) :
    ([∗list] q ∈ ms, msgOwn (GF := GF) q.loc (readyDq q.st) q.st ∗ msgCredits γ N q.st) ∗
      readyMsgs γ N id ms ⊢
    [∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ N id q.st ∗ msgCredits γ N q.st := by
  unfold readyMsgs
  refine BigSepL.bigSepL_sep_eqv_symm.1.trans (BigSepL.bigSepL_mono_of_forall ?_)
  intro _ _
  iintro ⟨⟨Ho, Hc⟩, Hs⟩
  iframe

end run

end kvdurable
end EtcdGrove
end Perennial
