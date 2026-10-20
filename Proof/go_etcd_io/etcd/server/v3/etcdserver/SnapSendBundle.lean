/-
**The merged snapshot as a network snapshot bundle** (D22 S-h, 2026-10-20; `notes/decisions.md`,
"D22 S-h carried out"): what `applyAll`'s `msgSnapC` branch (`server.go`; dead in the proof until
S-l lifts the no-snapshot mode) needs between `createMergedSnapshotMessage` and `sendMergedSnap`.
Lean-first (no Rocq counterpart).

* `isMessage_snap_voters`: the `.snap` clause of `isMessage` does not read the message's
  `voters` (the `ConfState` the merged message carries is `ep.confState`'s, not the storage's).
* `srvMergedBundle`: from the `MsgSnap` raft made (its `isRaftMsg`, its term's budget bound
  `termLB`), raft's commit invariant, a commit witness of its term `T` with a commit index `c ≥ ai`
  (D22l's bound: today the batch's `rnRtOk γ ap.raftTerm` gives one with no bound,
  `rnRtBound`), the applied committed prefix `A` (`|A| = ai`, last term `at`), the image's
  certificate `srvImage γ ai D` and the reader's streams, the merged message (`mergedSt`) is the
  network's snapshot bundle (`netSnapBundle (srvNet γ bud)`), which `SendSnapshot` takes: its
  protocol content minted by raft's `isMessage_snap_recontent` (D22 S-b), no `SentMsgOk` needed
  (outside the no-snapshot mode), the read credit `0` and no tickets.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvSnapSend
public import Proof.go_etcd_io.raft.v3.Protocol.SnapMint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- The `.snap` clause of `isMessage` does not read the `ConfState` lists or `AutoLeave`
(D22 S-b′ part 1: `Msg`'s `cl`/`al`, until then `voters`; S-b′'s certificate will). -/
theorem isMessage_snap_lists (γ : RaftNames) (m : Msg) (cl : CSLists) (al : Bool)
    (h : m.ty = .snap) :
    isMessage (GF := GF) γ { m with cl := cl, al := al } = isMessage γ m := by
  rcases m with ⟨ty, src, dst, term, reject, index, logterm, commit, rejecthint, entries, cl0, al0,
    ctx⟩
  simp only at h
  subst h
  rfl

end ghost

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
/-- **The recorded term's commit bound** (D22l, to be supplied): a commit witness of the term
`rt` with a commit index at least the applied index `ai`. The batch's `rnRtOk γ rt` (D22 S-b)
gives a witness at `rt` with no bound; D22l (`dlv` at `(delivered, phs)`) gives the bound. -/
def rnRtBound (γ : RaftNames) (rt ai : w64) : IProp GF :=
  iprop(∃ c : w64, commitWit γ rt c ∗ ⌜uint.Z ai ≤ uint.Z c⌝)

instance rnRtBound_persistent (γ : RaftNames) (rt ai : w64) :
    Persistent (rnRtBound (GF := GF) γ rt ai) := by
  unfold rnRtBound; infer_instance

/-- **The merged snapshot is the network's snapshot bundle** (see the file header). -/
theorem srvMergedBundle (γ : RaftNames) (bud : BudgetNames) (E : CoPset) (ml : Loc) (st : MsgSt)
    (sn0 : SnapshotM) (c : ConfStateM) (ai at_ : w64) (A : List EntryM) (rc : GoInterface)
    (D : backend.Data)
    (HE : ↑raftLogN ⊆ E) (Hty : st.msg.Type' = MsgSnap) (Hsn : st.snap = some sn0)
    (Hix : uint.Z sn0.Metadata'.Index' ≤ uint.Z ai)
    (HAlen : (A.length : Int) = uint.Z ai) (HAlast : A.getLast?.map EntryM.Term' = some at_) :
    ⊢ raftCommitInv (GF := GF) γ -∗ isRaftMsg γ st -∗ termLB bud st.msg.Term' -∗
      rnRtBound γ st.msg.Term' ai -∗ isCommitted γ A -∗
      msgOwn ml DFrac.discard (mergedSt st c ai at_) -∗
      backend.readerStreams rc (fun bs => backend.boltImage bs D) -∗ srvImage γ ai D ={E}=∗
      netSnapBundle (srvNet γ bud) ml rc := by
  iintro #Hinv #Hrm #Htlb #Hbnd #HA #Hml Hrs #Himg
  iunfold isRaftMsg at Hrm
  icases Hrm with ⟨%Hns, %Hsent, %a, %Habs, #Hmsgs⟩
  -- the abstraction of raft's `MsgSnap`
  have Ha : a = some (absSnap st.msg sn0 sn0.Metadata'.ConfState'.lists) := by
    rcases Habs with ⟨Hn, -⟩ | ⟨ty', Hty', Hne, -⟩ | ⟨sv, -, Hsv, rfl⟩
    · rw [Hty, mtypeOf_MsgSnap] at Hn; cases Hn
    · rw [Hty, mtypeOf_MsgSnap] at Hty'; cases Hty'; exact absurd rfl Hne
    · rw [Hsn] at Hsv; cases Hsv; rfl
  subst Ha
  simp only [Option.toList_some]
  icases BigSepL.bigSepL_cons.1 $$ Hmsgs with ⟨#Hm, -⟩
  iunfold rnRtBound at Hbnd
  icases Hbnd with ⟨%cw, #Hw, %Hac⟩
  -- the merged content: `isMessage_snap_recontent`, then the voters
  have Hterm : (absSnap st.msg sn0 sn0.Metadata'.ConfState'.lists).term = st.msg.Term' := rfl
  ihave #Hw' : commitWit γ (absSnap st.msg sn0 sn0.Metadata'.ConfState'.lists).term cw $$ []
  · rw [Hterm]; iexact Hw
  imod isMessage_snap_recontent γ E (absSnap st.msg sn0 sn0.Metadata'.ConfState'.lists) cw ai at_ A
    HE rfl Hix Hac HAlen HAlast $$ Hinv Hm Hw' HA with #Hm'
  have Hvo := isMessage_snap_lists (GF := GF) γ
    { absSnap st.msg sn0 sn0.Metadata'.ConfState'.lists with index := ai, logterm := at_ }
    (ConfStateM.lists c) c.AutoLeave' rfl
  imod rdCred_zero_upd γ with Hz
  imodintro
  iunfold netSnapBundle
  iexists mergedSt st c ai at_, SnapshotM.mk [] (SnapshotMetadataM.mk c ai at_), D
  iframe Hml Hrs
  isplitr
  · -- `□ N.P`: `isRaftMsg` and `termLB` of the merged message (same type and term)
    imodintro
    simp only [srvNet]
    isplitr
    · iunfold isRaftMsg
      isplitr
      · ipureintro; exact Hns
      isplitr
      · -- `SentMsgOk` reads only the message, which the merge keeps (D22 S-c: under the
        -- no-transfer mode alone, `MsgSnap` included)
        ipureintro
        exact Hsent
      iexists some (absSnap st.msg (SnapshotM.mk [] (SnapshotMetadataM.mk c ai at_))
        (ConfStateM.lists c))
      isplitr
      · ipureintro
        right; right
        exact ⟨_, by simp only [mergedSt]; rw [Hty]; exact mtypeOf_MsgSnap, rfl, rfl⟩
      simp only [Option.toList_some]
      iapply BigSepL.bigSepL_cons.2
      isplitl
      · have Heq : absSnap st.msg (SnapshotM.mk [] (SnapshotMetadataM.mk c ai at_))
            (ConfStateM.lists c) =
            { { absSnap st.msg sn0 sn0.Metadata'.ConfState'.lists with
                index := ai, logterm := at_ } with cl := ConfStateM.lists c, al := c.AutoLeave' } :=
            rfl
        rw [Heq, Hvo]
        iexact Hm'
      iapply BigSepL.bigSepL_nil.2; iempintro
    · simp only [mergedSt]; iexact Htlb
  isplitl [Hz]
  · -- `N.O`: the read credit `0` (not a `MsgReadIndex`), no tickets (not a `MsgProp`)
    simp only [srvNet, mergedSt]
    have h1 : st.msg.Type' ≠ MsgReadIndex := by rw [Hty]; simp [MsgSnap, MsgReadIndex]
    have h2 : st.msg.Type' ≠ MsgProp := by rw [Hty]; simp [MsgSnap, MsgProp]
    rw [if_neg h1]
    iframe Hz
    unfold stTks
    rw [if_neg h2]
    iempintro
  isplitr
  · ipureintro; exact ⟨Hty, rfl⟩
  simp only [srvNet]
  iexact Himg

end defs

end EtcdGrove
end Perennial
