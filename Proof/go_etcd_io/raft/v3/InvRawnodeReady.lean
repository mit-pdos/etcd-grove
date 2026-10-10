/-
**A `Ready` computed but not yet accepted (2026-10-10)**

`node.go`'s `run` does not call `RawNode.Ready`: it calls its two halves,
`readyWithoutAccept` (when `HasReady`), hands the `Ready` to the application
(`readyc <- rd`), and only then `acceptReady(rd)`, with no raft step in between.
`ownRawNodeReady γ rn id rs rd ce es` is the node between the two: `ownRawNode γ rn id rs`
with the outbox `r.msgs`' slice given up to `rd.Messages` (`readyWithoutAccept` builds
`rd.Messages` in place from `r.msgs`, and `acceptReady` only sets the field to `nil`), and
what `acceptReady` reads of `rd` recorded: the soft state pointer read-only (or `nil`), no
snapshot nor read states, the committed entries `ce` (read-only, with the slice's capacity,
which `acceptReady` hands to the queued `MsgStorageApplyResp`) and the entries `es` handed
out for the storage. The node itself is as `readyWithoutAccept` found it (it only reads);
`acceptReady` takes the predicate back to `ownRawNode` at the post-`Ready` state.

`ownRaftPhysReady` is `ownRaftPhys` opened as `ownRaftPhys_view` opens it, without the
contents of `r.msgs`' slice (the field is kept): what `acceptReady` needs to close it with
empty queues.

**Abandoning a `Ready` (2026-10-10).** `node.go` recomputes `rd` when its `select` takes
another case, and steps the node meanwhile: the computed `Ready` is dropped, and the node
must be whole again. `ownRawNodeReady_abandon` gives it back, `ownRawNode γ rn id rs`, for
the messages handed out (`rd.Messages ↦* ms` with its capacity). The messages are built by
appending onto `r.msgs`, which Go may do in place (into `r.msgs`' capacity) or by copying
into a new array (leaving the old one untouched); either way `r.msgs`' slice and capacity
can be recovered from the new ones (Perennial's `wp_slice_append_undo`). So
`ownRaftPhysReady` keeps a wand `Hundo` from `rd.Messages`' contents and capacity back to
`r.msgs`' (indexed by the slice and the list it was built for, `ms`, a parameter of
`ownRawNodeReady`), and the queues' term bound (`OutTermOk`) for the wand `Hclose`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section rawnodeReady
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- The raft struct at `s`, open as `ownRaftPhys_view` opens it, with the contents of the
outbox `r.msgs` handed out (to a `Ready`'s `Messages`, the slice `msl` holding `ms`), and
the way back from `msl` to `r.msgs`' slice (`Hundo`): see the file header. -/
def ownRaftPhysReady (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (msl : GoSlice)
    (ms : List raftpb.Message) : IProp GF :=
  iprop(∃ (rsl sl1 sl2 : GoSlice) (ms1 ms2 : List raftpb.Message),
    "Hf_id" ∷ r.[raft, go!"id"] ↦ id ∗
    "Hf_Term" ∷ r.[raft, go!"Term"] ↦ s.term ∗
    "Hf_Vote" ∷ r.[raft, go!"Vote"] ↦ s.vote ∗
    "Hf_readStates" ∷ r.[raft, go!"readStates"] ↦ rsl ∗
    "%Hrs" ∷ ⌜rsl.len = W64 0⌝ ∗
    "Hf_raftLog" ∷ r.[raft, go!"raftLog"] ↦ s.log ∗
    "Hf_state" ∷ r.[raft, go!"state"] ↦ stateW64 s.role ∗
    "Hf_lead" ∷ r.[raft, go!"lead"] ↦ s.lead ∗
    "Hf_msgs" ∷ r.[raft, go!"msgs"] ↦ sl1 ∗
    "Hf_msgsAA" ∷ r.[raft, go!"msgsAfterAppend"] ↦ sl2 ∗ "HmsgsAA" ∷ sl2 ↦* ms2 ∗
    "HmsgsAA_cap" ∷ ownSliceCap raftpb.Message sl2 (DFrac.own 1) ∗
    "#Houtbox" ∷ outboxRel s.outbox ms1 ms2 ∗
    "%HmsgsAA_ok" ∷ ⌜∀ m ∈ ms2, AAMsgOk id s.term m⌝ ∗
    "%Hout_term" ∷ ⌜∀ m ∈ ms1 ++ ms2, OutTermOk s.prevote s.term m⌝ ∗
    "Hundo" ∷ (msl ↦* ms -∗ ownSliceCap raftpb.Message msl (DFrac.own 1) -∗
               sl1 ↦* ms1 ∗ ownSliceCap raftpb.Message sl1 (DFrac.own 1)) ∗
    "Hlog" ∷ ownRaftLog s.log s.logst ∗
    "Hclose" ∷ (∀ (sl1' sl2' : GoSlice) (ms1' ms2' : List raftpb.Message) (o : List Msg)
                  (ls' : LogState),
        r.[raft, go!"id"] ↦ id -∗
        r.[raft, go!"Term"] ↦ s.term -∗
        r.[raft, go!"Vote"] ↦ s.vote -∗
        r.[raft, go!"readStates"] ↦ rsl -∗
        r.[raft, go!"raftLog"] ↦ s.log -∗
        r.[raft, go!"state"] ↦ stateW64 s.role -∗
        r.[raft, go!"lead"] ↦ s.lead -∗
        r.[raft, go!"msgs"] ↦ sl1' -∗ sl1' ↦* ms1' -∗
        ownSliceCap raftpb.Message sl1' (DFrac.own 1) -∗
        r.[raft, go!"msgsAfterAppend"] ↦ sl2' -∗ sl2' ↦* ms2' -∗
        ownSliceCap raftpb.Message sl2' (DFrac.own 1) -∗
        outboxRel o ms1' ms2' -∗
        ⌜∀ m ∈ ms2', AAMsgOk id s.term m⌝ -∗
        ⌜∀ m ∈ ms1' ++ ms2', OutTermOk s.prevote s.term m⌝ -∗
        ownRaftLog s.log ls' -∗
        ownRaftPhys cfg r id { s with outbox := o, logst := ls' }))

/-- The node between `readyWithoutAccept` and `acceptReady` (see the file header): the
conjuncts of `ownRawNode γ rn id rs` at a state `s` with an empty queue and nothing
unpersisted (`Ready`'s premises), the struct open without the outbox's contents
(`ownRaftPhysReady`), and what `acceptReady` reads of `rd`: `rd.SoftState` `nil` or
read-only, no snapshot nor read states, the committed entries `ce` extending
`rs.delivered` (`isCommitted`) and the next ones of the log (`logCommittedEnts`), with
their slice's capacity, and the entries `es` handed out (`nextUnstable`). `ms` are the
messages handed out in `rd.Messages`, which `ownRawNodeReady_abandon` takes back
(2026-10-10). -/
def ownRawNodeReady (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready)
    (ce es : List raftpb.Entry) (ms : List raftpb.Message) : IProp GF :=
  iprop(∃ (s : NState) (ps : PState) (rnv : RawNode) (sv : SoftState),
  "Hrn" ∷ rn ↦ rnv ∗
  "Hphys" ∷ ownRaftPhysReady γ.reCfg rnv.raft' id s rd.Messages' ms ∗
  "Hghost" ∷ ownRaftGhost γ id ps ∗
  "%Hrel" ∷ ⌜NStateRel s ps⌝ ∗
  "%Hin" ∷ ⌜id ∈ γ.reCfg⌝ ∗
  "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* ([] : List raftpb.Message) ∗
  "Hsteps_cap" ∷ ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) ∗
  "#Hcommitted" ∷ isCommitted γ (rs.delivered ++ ce) ∗
  "#Hstrecs" ∷ storedRecs γ s.logst.prev s.logst.stored ∗
  "%Hdlen" ∷ ⌜rs.delivered.length = (uint.Z s.logst.applying).toNat⌝ ∗
  "%Hunp" ∷ ⌜s.logst.unpersisted = []⌝ ∗
  "%Hsnap" ∷ ⌜s.logst.snap = none⌝ ∗
  "%Htrm" ∷ ⌜rs.term = s.term⌝ ∗
  "%Hstor" ∷ ⌜rs.storage = s.logst.storage⌝ ∗
  "%Hpvoff" ∷ ⌜s.prevote = false⌝ ∗
  -- the `Ready`, as `acceptReady` reads it
  "#Hrdsoft" ∷ (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) ∗
  "%Hrdz" ∷ ⌜rd.Snapshot' = zero_val raftpb.Snapshot ∧ rd.ReadStates' = slice.nil⌝ ∗
  "#Hce" ∷ rd.CommittedEntries' ↦*□ ce ∗
  "Hce_cap" ∷ ownSliceCap raftpb.Entry rd.CommittedEntries' (DFrac.own 1) ∗
  "%Hcepre" ∷ ⌜ce <+: logCommittedEnts s.logst⌝ ∗
  "%Hes" ∷ ⌜es = nextUnstable s.logst⌝)

/-- Abandoning a computed `Ready` (2026-10-10; see the file header): with the messages it
handed out given back, the node is as before `readyWithoutAccept` (which changed nothing:
Go's "read-only operation"). The premises are `readyWithoutAccept`'s. Everything else
`readyWithoutAccept` allocated (the `Ready` itself, the committed entries' slice) is
dropped. -/
theorem ownRawNodeReady_abandon (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List raftpb.Entry) (ms : List raftpb.Message)
    (Hsteps0 : rs.steps = []) (Hunp0 : rs.unpersisted = []) :
    ⊢ rd.Messages' ↦* ms -∗ ownSliceCap raftpb.Message rd.Messages' (DFrac.own 1) -∗
      ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms -∗ ownRawNode γ rn id rs := by
  iintro Hmsgs Hmsgs_cap H
  iunfold ownRawNodeReady at H
  icases H with ⟨%s, %ps, %rnv, %sv, H⟩
  iNamed H
  iunfold ownRaftPhysReady at Hphys
  icases Hphys with ⟨%rsl, %sl1, %sl2, %ms1, %ms2, Hphys⟩
  iNamed Hphys
  icases Hundo $$ Hmsgs Hmsgs_cap with ⟨Hm1, Hc1⟩
  ihave Hphys := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst Hf_id Hf_Term Hf_Vote
    Hf_readStates Hf_raftLog Hf_state Hf_lead Hf_msgs Hm1 Hc1 Hf_msgsAA HmsgsAA HmsgsAA_cap
    Houtbox %HmsgsAA_ok %Hout_term Hlog
  ihave #Hdeliv : isCommitted γ rs.delivered $$ []
  · iapply isCommitted_mono γ rs.delivered (rs.delivered ++ ce) (List.prefix_append _ _)
      $$ Hcommitted
  ihave Hpend : ([∗list] _k ↦ m;p ∈ ([] : List raftpb.Message);rs.steps,
      pendingRel γ id m p) $$ []
  · rw [Hsteps0]
    iapply (BigSepL2.bigSepL2_nil (Φ := fun _ m p => pendingRel (GF := GF) γ id m p)).2
    iempintro
  ihave Hpown : ([∗list] _k ↦ m;p ∈ ([] : List raftpb.Message);rs.steps,
      pendingOwn (GF := GF) m p) $$ []
  · rw [Hsteps0]
    iapply (BigSepL2.bigSepL2_nil (Φ := fun _ m p => pendingOwn (GF := GF) m p)).2
    iempintro
  iapply ownRawNode_intro γ rn id rs s ps rnv sv [] Hrel Hin Hasync Hdlen
    (Hunp0.trans Hunp.symm) Hsnap (by rw [Hsteps0]; trivial) Htrm Hstor Hpvoff
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

end rawnodeReady

end EtcdGrove
end Perennial
