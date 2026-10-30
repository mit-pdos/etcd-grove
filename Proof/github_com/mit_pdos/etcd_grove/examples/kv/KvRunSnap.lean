/-
Lean-first (no Rocq counterpart).

# `run`'s view of its node and a snapshot `Ready` (2026-10-30, stage P of the client repair:
kvreconf's `RunApply`/`RunSnap`, at kv's storage)

- the applier's view of its node (`appNode`) carried to a longer delivered log (`appNode_extend`),
  opened for `Advance` (`appNode_open`), and after a snapshot `Ready`'s `Advance` (`appNode_snap`);
- the bound on a delivered log with an entry frozen above the compaction point (`frozenTo_len`);
- `Append` after a snapshot (`snapAppend_pre`/`snapAppend_post`), `Advance`'s receipt for it
  (`kv_snapReceipt`), nothing frozen above a snapshot's index (`frozenTo_snap`);
- the store's committed logs hold no conf entry (`kv_noConf`): a committed conf entry is raft's
  empty `ConfChangeV2` (`kv_committed_conf`), which no position of the voters' (simple) membership
  holds (`committed_emptyV2_joint`), and the membership stays the voters' along a log without conf
  entries (`confAt_noConf`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.KvRunFrozen
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Reconf

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3


section apply
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]


/-- `skippedIn` reads the entries below its end only: it carries to a longer log. -/
theorem skippedIn_prefix (γ : Cluster) (l l' : List LogEntry) (a b : Nat) (hp : l <+: l')
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
theorem appNode_extend (γr : RKVNames) (n : Loc) (l l' : List LogEntry) (k : Nat) (m : Membership)
    (hp : l <+: l') (hk : k ≤ l.length) :
    appNode (GF := GF) γr n l k m ∗ deliveredLogLb n γr.cluster kvRaftN l' ⊢ appNode γr n l' k m := by
  unfold appNode
  iintro ⟨⟨%v, Hc, -, #Hs, %Hv⟩, #Hd⟩
  iexists v
  iframe Hc Hd
  isplitl []
  · iapply skippedIn_prefix _ l l' _ _ hp hk $$ Hs
  ipureintro; exact Hv

/-- The applier's view opened for `Advance`: the node's configuration view, every conf entry
from its index skipped. -/
theorem appNode_open (γr : RKVNames) (n : Loc) (l : List LogEntry) (k : Nat) (m : Membership) :
    appNode (GF := GF) γr n l k m ⊢ ∃ v : ConfigView, nodeConfig n γr.cluster kvRaftN v ∗
      skippedIn γr.cluster l v.applied k ∗
      (nodeConfig n γr.cluster kvRaftN v -∗ appNode γr n l k m) := by
  unfold appNode
  iintro ⟨%v, Hc, #Hd, #Hs, %Hv⟩
  iexists v
  iframe Hc Hs
  iintro Hc
  iexists v
  iframe Hc Hd Hs
  ipureintro; exact Hv

/-- A delivered log with an entry frozen above the compaction point is shorter than `2^61`. -/
theorem frozenTo_len (γs : MemStorNames) (c : Nat) (D : List LogEntry) :
    frozenTo (GF := GF) γs c D ⊢ ⌜c < D.length → D.length < 2 ^ 61⌝ := by
  unfold frozenTo
  iintro #H
  ihave %Hb := memLog_bound _ _ _ _ $$ H
  ipureintro
  intro hc
  rw [List.length_drop, kv_toEntries_length] at Hb
  rcases Hb with h | h
  · have := congrArg List.length h
    rw [List.length_drop, kv_toEntries_length] at this
    simp at this; omega
  · omega

end apply


section snap

variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]


/-- Two committed logs of the same length are the same. -/
theorem committed_eq (γ : Cluster) (l1 l2 : List LogEntry) (h : l1.length = l2.length) :
    isCommittedLogLb (GF := GF) γ l1 ∗ isCommittedLogLb γ l2 ⊢ ⌜l1 = l2⌝ := by
  iintro ⟨#H1, #H2⟩
  ihave %Hag := isCommittedLogLb_agree γ l1 l2 $$ [H1 H2]
  · iframe H1 H2
  ipureintro
  rcases Hag with hp | hp
  · exact hp.eq_of_length h
  · exact (hp.eq_of_length h.symm).symm

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
theorem kv_snapReceipt (st ms : Loc) (γs : MemStorNames) (l : SnapLoan) (es : List EntryM) :
    ⊢ kvStorRec (GF := GF) st ms γs -∗ ownSnapM l.ptr (DFrac.own (Qp.half 1)) l.snap -∗
      memCompacted γs (uint.nat l.snap.Metadata'.Index') -∗
      memLog γs (uint.nat l.snap.Metadata'.Index') DFrac.discard [memDummy l.snap] -∗
      memLog γs (uint.nat l.snap.Metadata'.Index' + 1) (DFrac.own 1) es -∗
      memEnd γs (uint.nat l.snap.Metadata'.Index' + 1 + es.length) -∗
      snapReceipt (kvStorIface st) l es := by
  iintro #Hrec Hs #Hc #Hd Hl He
  unfold snapReceipt
  iframe Hs
  isplitl []
  · iapply kvStorCompacted_of st ms γs _ $$ Hrec Hc
  isplitl []
  · iexists memDummy l.snap
    isplitr
    · ipureintro; rfl
    iapply kvStorLog_of st ms γs _ _ _ $$ Hrec Hd
  ihave Hl := kvStorLog_of st ms γs _ _ _ $$ Hrec Hl
  ihave He := kvStorEnd_of st ms γs _ $$ Hrec He
  iframe Hl He

/-- The applier's view after a snapshot `Ready`'s `Advance`: at the snapshot's index, the end of
the delivered log. -/
theorem appNode_snap (γr : RKVNames) (n : Loc) (L : List LogEntry) (i : Nat) (m : Membership)
    (h : L.length = i) :
    nodeConfig (GF := GF) n γr.cluster kvRaftN ⟨i, m⟩ ∗ deliveredLogLb n γr.cluster kvRaftN L ⊢
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
theorem frozenTo_snap (γs : MemStorNames) (L : List LogEntry) (c : Nat) (h : L.length = c) :
    ⊢ frozenTo (GF := GF) γs c L := by
  unfold frozenTo
  rw [List.drop_eq_nil_of_le (by rw [kv_toEntries_length]; omega)]
  iapply memLog_nil

end snap

section noconf
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- Every conf entry of a committed log is raft's empty `ConfChangeV2` (`kv_committed_conf`, for
the whole log at once). -/
theorem kv_committed_conf_all (γr : RKVNames) (l : List LogEntry) (E : CoPset) (HE : ↑rkvN ⊆ E) :
    ⊢ rkvInv (GF := GF) γr -∗ isCommittedLogLb γr.cluster l ={E}=∗
      ⌜∀ e, e ∈ l → e.isConfChange → e.isEmptyV2⌝ := by
  iintro #Hinv #Hl
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %S, %Mi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, HS, HMi, HO, %Hok, %Hodm, %Hrm⟩
  ihave %Hpre := ownCommittedOps_lb_prefix γr.cluster ops l $$ [Hops Hl]
  · iframe Hops Hl
  imod Hclose $$ [Hops Hv HU HS HMi HO Hsl] with -
  · inext
    iexists ops, S, Mi, O, U
    iframe Hsl
    unfold kvCore
    iframe Hops Hv HU HS HMi HO
    ipureintro; exact ⟨Hok, Hodm, Hrm⟩
  imodintro
  ipureintro
  intro e Hel Hcc
  have Hne : e.type ≠ W32 0 := by
    rcases Hcc with h | h <;> rw [h] <;> intro h' <;> revert h' <;> word
  have Hnf : ¬ e.isFiller := fun h => Hne h.2
  by_cases Hev : e.isEmptyV2
  · exact Hev
  · have Hin : e ∈ ops := Hpre.subset (List.mem_filter.mpr ⟨Hel, by simp [Hnf, Hev]⟩)
    exact (Hne (Hrm e Hin)).elim

/-- No position of a committed log whose conf entries are all empty `ConfChangeV2`s holds a conf
entry, from the voters' membership at its start. -/
theorem kv_noConf_upto (γr : RKVNames) (l : List LogEntry)
    (Hev : ∀ e, e ∈ l → e.isConfChange → e.isEmptyV2) :
    ∀ k, k ≤ l.length → isCluster (GF := GF) γr.cluster kvRaftN ∗ isCommittedLogLb γr.cluster l ∗
      confAt γr.cluster 0 kvMembership ⊢ ⌜NoConfChangeIn l 0 k⌝
  | 0, _ => by
    iintro -
    ipureintro; exact noConf_empty l 0
  | k + 1, hk => by
    iintro #⟨Hc, Hl, H0⟩
    ihave %IH := kv_noConf_upto γr l Hev k (by omega) $$ [Hc Hl H0]
    · iframe Hc Hl H0
    have hkl : k < l.length := by omega
    obtain ⟨e, he⟩ : ∃ e, l[k]? = some e := ⟨_, List.getElem?_eq_getElem hkl⟩
    by_cases hcc : e.isConfChange
    · ihave #Hk := confAt_noConf γr.cluster l 0 k kvMembership IH (Nat.zero_le _) (by omega)
        $$ [Hl H0]
      · iframe Hl H0
      ihave %Hj := committed_emptyV2_joint γr.cluster kvRaftN l k e kvMembership he
        (Hev e (List.mem_of_getElem? he) hcc) $$ [Hc Hl Hk]
      · iframe Hc Hl Hk
      exact absurd Hj (fun h => h rfl)
    · ipureintro; exact noConf_snoc l 0 k e IH he hcc

/-- **The store's committed logs hold no conf entry** (see the file header), and every position
of one keeps the voters' membership. -/
theorem kv_noConf (γr : RKVNames) (l : List LogEntry) (E : CoPset) (HE : ↑rkvN ⊆ E) :
    ⊢ rkvInv (GF := GF) γr -∗ kvCluster γr -∗ isCommittedLogLb γr.cluster l ={E}=∗
      ⌜NoConfChangeIn l 0 l.length⌝ ∗ confAt γr.cluster l.length kvMembership := by
  iintro #Hinv #Hcl #Hl
  imod kv_committed_conf_all γr l E HE $$ Hinv Hl with %Hev
  unfold kvCluster
  icases Hcl with ⟨#Hc, -, #H0, -⟩
  ihave %Hnc := kv_noConf_upto γr l Hev l.length (Nat.le_refl _) $$ [Hc Hl H0]
  · iframe Hc Hl H0
  imodintro
  isplitl []
  · ipureintro; exact Hnc
  iapply confAt_noConf γr.cluster l 0 l.length kvMembership Hnc (Nat.zero_le _) (Nat.le_refl _)
  iframe Hl H0

end noconf

end kv
end EtcdGrove
end Perennial
