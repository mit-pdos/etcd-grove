/-
Lean-first (no Rocq counterpart).

# A snapshot `Ready` (2026-10-30, kvreconf's `run`)

What `run` uses to install a snapshot the node hands out (`readySnap (some l)`):
- `kvr_snap_recv`: the snapshot's certificate (`snapshotCert`) is the storage's `J.SV`
  (`snapshotValid`), and its record in the store's registry (`kvrSnapInv`, `snapMade_elem`) says
  its data encodes the state of the delivered log (`kvSnapOk`) and bounds its membership: what
  `decodeState` and `install` need;
- `snapAppend_pre`/`snapAppend_post`: `Append` at the entry after the snapshot's index, where the
  storage's range is empty (`memLog_nil`) and ends after the dummy;
- `kvr_snapReceipt`: what `Advance` takes back (`snapReceipt`), at the wrapper's interface;
- `appNode_snap`, `frozenTo_snap`: the applier's view and frozen range at the snapshot's index.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunApply

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section snap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

instance kvrSnapRecOk_timeless (γr : RNames) (s : SnapRec) :
    Timeless (kvrSnapRecOk (GF := GF) γr s) := by
  unfold kvrSnapRecOk; infer_instance

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

/-- **A snapshot handed out by the node** (see the file header), at the committed log `L` of its
index. -/
theorem kvr_snap_recv (γr : RNames) (vs : List w64) (sv : SnapshotM) (L : List LogEntry)
    (Hpos : 0 < uint.Z sv.Metadata'.Index') (Hi : uint.Z sv.Metadata'.Index' < 2 ^ 61)
    (Hlen : L.length = uint.nat sv.Metadata'.Index') :
    ⊢ kvrCluster (GF := GF) γr vs -∗ isCommittedLogLb γr.cluster L -∗
      snapshotCert γr.cluster kvrRaftN (snapTrip sv sv.Metadata'.ConfState'.lists) ={⊤}=∗
      snapshotValid γr.cluster sv ∗ ∃ m : Membership, confAt γr.cluster L.length m ∗
        ⌜confStateIs sv.Metadata'.ConfState' m ∧ GMap.size m.ids < 2 ^ 61 ∧ kvSnapOk L sv.Data'⌝ := by
  iintro #Hcl #HL #Hcert
  unfold kvrCluster
  icases Hcl with ⟨#Hc, -, -, #Hinv, -⟩
  ihave #Hsv := snapshotCert_valid γr.cluster kvrRaftN sv Hpos Hi $$ [Hc Hcert]
  · iframe Hc Hcert
  ihave #Hsv' := Hsv
  unfold snapshotValid
  icases Hsv' with ⟨%l1, %m1, #Hl1, #Hca1, #Hmade, %Hp⟩
  ihave %Heq := committed_eq γr.cluster l1 L (by rw [Hlen]; exact Hp.1) $$ [Hl1 HL]
  · iframe Hl1 HL
  subst Heq
  unfold kvrSnapInv
  iinv Hinv with Hb Hclose
  icases Hb with ⟨%S, >Hown, >#HS⟩
  ihave ⟨⟨Hown, -⟩, %Hin⟩ := persistent_entails_left (snapMade_elem γr.cluster S _) $$ [Hown Hmade]
  · iframe Hown Hmade
  ihave #Hrec := BigSepL.bigSepL_mem (Φ := fun s => kvrSnapRecOk (GF := GF) γr s) Hin $$ HS
  imod Hclose $$ [Hown] with -
  · inext
    iexists S
    iframe Hown HS
  imodintro
  iframe Hsv
  iexists m1
  iframe Hca1
  unfold kvrSnapRecOk
  icases Hrec with ⟨%L2, #HL2, -, %Hr⟩
  simp only at Hr
  ihave %Heq := committed_eq γr.cluster L2 l1 Hr.1 $$ [HL2 Hl1]
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
theorem kvr_snapReceipt (st ms : Loc) (γs : MemStorNames) (l : SnapLoan) (es : List EntryM) :
    ⊢ kvrStorRec (GF := GF) st ms γs -∗ ownSnapM l.ptr (DFrac.own (Qp.half 1)) l.snap -∗
      memCompacted γs (uint.nat l.snap.Metadata'.Index') -∗
      memLog γs (uint.nat l.snap.Metadata'.Index') DFrac.discard [memDummy l.snap] -∗
      memLog γs (uint.nat l.snap.Metadata'.Index' + 1) (DFrac.own 1) es -∗
      memEnd γs (uint.nat l.snap.Metadata'.Index' + 1 + es.length) -∗
      snapReceipt (kvrStorIface st) l es := by
  iintro #Hrec Hs #Hc #Hd Hl He
  unfold snapReceipt
  iframe Hs
  isplitl []
  · iapply kvrStorCompacted_of st ms γs _ $$ Hrec Hc
  isplitl []
  · iexists memDummy l.snap
    isplitr
    · ipureintro; rfl
    iapply kvrStorLog_of st ms γs _ _ _ $$ Hrec Hd
  ihave Hl := kvrStorLog_of st ms γs _ _ _ $$ Hrec Hl
  ihave He := kvrStorEnd_of st ms γs _ $$ Hrec He
  iframe Hl He

/-- The applier's view after a snapshot `Ready`'s `Advance`: at the snapshot's index, the end of
the delivered log. -/
theorem appNode_snap (γr : RNames) (n : Loc) (L : List LogEntry) (i : Nat) (m : Membership)
    (h : L.length = i) :
    nodeConfig (GF := GF) n γr.cluster kvrRaftN ⟨i, m⟩ ∗ deliveredLogLb n γr.cluster kvrRaftN L ⊢
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
  rw [List.drop_eq_nil_of_le (by rw [kvr_toEntries_length]; omega)]
  iapply memLog_nil

end snap

end kvreconf
end EtcdGrove
end Perennial
