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

/-- What `acceptReady` needs of the committed entries `ce` a `Ready` hands out
(2026-10-10): they are the next ones after `applying`, up to at most `committed` -- its
`acceptApplying` moves `applying` to the last one's index, and the queued
`MsgStorageApplyResp` acknowledges them. Until 2026-10-10 `ownRawNodeReady` recorded
`ce <+: logCommittedEnts s.logst`, which implies this (`ceOk_of_prefix`); this weaker fact
survives the steps `node.go` takes after abandoning a `Ready` (they keep `applying` and do
not lower `committed`), so that an abandoned `Ready` can still be accepted
(`ownRawNodeIdle_ready`). -/
def CeOk (ls : LogState) (ce : List raftpb.Entry) : Prop :=
  ∀ e, ce.getLast? = some e →
    uint.Z ls.applying < uint.Z e.Index' ∧ uint.Z e.Index' ≤ uint.Z ls.committed ∧
    uint.Z e.Index' = uint.Z ls.applying + (ce.length : Int)

theorem ceOk_of_prefix (ls : LogState) (ce : List raftpb.Entry)
    (Hidx : LogIndicesOk ls.prev (ls.sents ++ ls.uents))
    (Hle : uint.Z ls.prev.index' ≤ uint.Z ls.applying ∧ uint.Z ls.applying ≤ uint.Z ls.committed)
    (Hnw : uint.Z ls.committed + 1 < 2 ^ 64)
    (Hce : ce <+: logCommittedEnts ls) : CeOk ls ce := by
  intro e Hl
  unfold logCommittedEnts plogFrom at Hce
  have Hk : (uint.Z (ls.applying + W64 1) - uint.Z ls.prev.index' - 1).toNat
      = (uint.Z ls.applying - uint.Z ls.prev.index').toNat := by word
  rw [Hk] at Hce
  obtain ⟨ce0, rfl⟩ := List.getLast?_eq_some_iff.1 Hl
  have Hlen := Hce.length_le
  simp only [List.length_append, List.length_singleton, List.length_take] at Hlen
  have Hlk : (ce0 ++ [e])[ce0.length]? = some e := by simp
  have H1 := prefix_getElem? Hce Hlk
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop] at H1
  have H2 := Hidx _ _ H1
  push_cast at H2
  simp only [List.length_append, List.length_singleton]
  omega

/-- The raft struct at `s`, open as `ownRaftPhys_view` opens it, with the contents of the
outbox `r.msgs` handed out (to a `Ready`'s `Messages`, the slice `msl` holding `ms`), and
the way back from `msl` to `r.msgs`' slice (`Hundo`): see the file header. Since
2026-10-10 also the ghost lower bounds (`NGhost`, `Hgh_out`, `Hgh_unst`), and that the
messages handed out are at most those queued (`Hmslen`), which the wand `Hclose` lets
raise (`ownRawNodeReady_abandon`). -/
def ownRaftPhysReady (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (msl : GoSlice)
    (ms : List raftpb.Message) : IProp GF :=
  iprop(∃ (rsl sl1 sl2 : GoSlice) (ms1 ms2 : List raftpb.Message),
    "#Hf_id" ∷ r.[raft, go!"id"] ↦□ id ∗
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
    "%Hgh_out" ∷ ⌜s.gh.outlb ≤ ms1.length + ms2.length⌝ ∗
    "%Hgh_unst" ∷ ⌜LogGhOk s s.logst⌝ ∗
    "%Hmslen" ∷ ⌜ms.length ≤ ms1.length + ms2.length⌝ ∗
    "Hundo" ∷ (msl ↦* ms -∗ ownSliceCap raftpb.Message msl (DFrac.own 1) -∗
               sl1 ↦* ms1 ∗ ownSliceCap raftpb.Message sl1 (DFrac.own 1)) ∗
    "Hlog" ∷ ownRaftLog s.log s.logst ∗
    "Hclose" ∷ (∀ (sl1' sl2' : GoSlice) (ms1' ms2' : List raftpb.Message) (o : List Msg)
                  (ls' : LogState) (g : NGhost),
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
        ⌜g.outlb ≤ ms1'.length + ms2'.length⌝ -∗
        ⌜g.unst = true → nextUnstable ls' ≠ [] ∨ ls'.snap ≠ none⌝ -∗
        ownRaftLog s.log ls' -∗
        ownRaftPhys cfg r id { s with outbox := o, logst := ls', gh := g }))

/-- The node between `readyWithoutAccept` and `acceptReady` (see the file header): the
conjuncts of `ownRawNode γ rn id rs` at a state `s` with an empty queue and nothing
unpersisted (`Ready`'s premises), the struct open without the outbox's contents
(`ownRaftPhysReady`), and what `acceptReady` reads of `rd`: `rd.SoftState` `nil` or
read-only, no snapshot nor read states, the committed entries `ce` extending
`rs.delivered` (`isCommitted`) and the next ones after `applying` (`CeOk`), with their
slice's capacity, and the entries `es` handed out (`nextUnstable`). `ms` are the messages
handed out in `rd.Messages`, which `ownRawNodeReady_abandon` takes back (2026-10-10). -/
def ownRawNodeReady (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready)
    (ce es : List raftpb.Entry) (ms : List raftpb.Message) : IProp GF :=
  iprop(∃ (s : NState) (ps : PState) (rnv : RawNode) (sv : SoftState),
  "Hrn" ∷ rawNodeOwn rn rnv ∗
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
  "%Hrs_out" ∷ ⌜rs.outlb = s.gh.outlb⌝ ∗
  "%Hrs_unst" ∷ ⌜rs.unst = s.gh.unst⌝ ∗
  "%Hrs_clb" ∷ ⌜uint.Z rs.clb ≤ uint.Z s.logst.committed⌝ ∗
  -- the `Ready`, as `acceptReady` reads it
  "#Hrdsoft" ∷ (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) ∗
  "%Hrdz" ∷ ⌜rd.Snapshot' = zero_val raftpb.Snapshot ∧ rd.ReadStates' = slice.nil⌝ ∗
  "#Hce" ∷ rd.CommittedEntries' ↦*□ ce ∗
  "Hce_cap" ∷ ownSliceCap raftpb.Entry rd.CommittedEntries' (DFrac.own 1) ∗
  "%Hceok" ∷ ⌜CeOk s.logst ce⌝ ∗
  "%Hes" ∷ ⌜es = nextUnstable s.logst⌝)

/-- Abandoning a computed `Ready` (2026-10-10; see the file header): with the messages it
handed out given back, the node is as before `readyWithoutAccept` (which changed nothing:
Go's "read-only operation"), but for the lower bounds (`RNState.outlb`, `unst`, `clb`),
raised to what the `Ready` held: at least as many messages as it handed out are queued,
unstable entries are still to be handed out if it handed some out, and its committed
entries are below the commit index. Every step keeps these, so if `HasReady` later finds
nothing new (`ownRawNodeIdle`), the `Ready` held no messages and no entries, and its
committed entries are still the next ones (`ownRawNodeIdle_ready`): `node.go`'s `run`
may then send it after all, as it does. The premises are `readyWithoutAccept`'s.
Everything else `readyWithoutAccept` allocated (the `Ready` itself, the committed
entries' slice) is dropped. -/
theorem ownRawNodeReady_abandon (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List raftpb.Entry) (ms : List raftpb.Message)
    (Hsteps0 : rs.steps = []) (Hunp0 : rs.unpersisted = []) :
    ⊢ rd.Messages' ↦* ms -∗ ownSliceCap raftpb.Message rd.Messages' (DFrac.own 1) -∗
      ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms -∗
      ∃ (n : Nat) (u : Bool) (c : w64),
        ⌜ms.length ≤ n ∧ (es ≠ [] → u = true) ∧
         (∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z c ∧
           uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int))⌝ ∗
        ownRawNode γ rn id { rs with outlb := n, unst := u, clb := c } := by
  iintro Hmsgs Hmsgs_cap H
  iunfold ownRawNodeReady at H
  icases H with ⟨%s, %ps, %rnv, %sv, H⟩
  iNamed H
  iunfold ownRaftPhysReady at Hphys
  icases Hphys with ⟨%rsl, %sl1, %sl2, %ms1, %ms2, Hphys⟩
  iNamed Hphys
  icases Hundo $$ Hmsgs Hmsgs_cap with ⟨Hm1, Hc1⟩
  let g : NGhost := { outlb := ms1.length + ms2.length,
                      unst := decide (nextUnstable s.logst ≠ []) }
  ihave Hphys := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst %g Hf_Term Hf_Vote
    Hf_readStates Hf_raftLog Hf_state Hf_lead Hf_msgs Hm1 Hc1 Hf_msgsAA HmsgsAA HmsgsAA_cap
    Houtbox %HmsgsAA_ok %Hout_term %(Nat.le_refl _)
    %(fun h => .inl (of_decide_eq_true h)) Hlog
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
  iexists ms1.length + ms2.length, decide (nextUnstable s.logst ≠ []), s.logst.committed
  isplitr
  · ipureintro
    refine ⟨Hmslen, fun h => by rw [Hes] at h; exact decide_eq_true h, fun e He => ?_⟩
    obtain ⟨-, H2, H3⟩ := Hceok e He
    refine ⟨H2, ?_⟩
    rw [H3, Hdlen]
    have := uint_Z_nonneg s.logst.applying
    omega
  let rs' : RNState :=
    { rs with outlb := ms1.length + ms2.length, unst := decide (nextUnstable s.logst ≠ []),
              clb := s.logst.committed }
  let s' : NState := { s with outbox := s.outbox, logst := s.logst, gh := g }
  iapply ownRawNode_intro γ rn id rs' s' ps rnv sv [] Hrel Hin Hasync Hdlen
    (Hunp0.trans Hunp.symm) Hsnap (by show StepsOk _ rs.steps; rw [Hsteps0]; trivial) Htrm
    Hstor Hpvoff rfl rfl
    (Int.le_refl _)
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

/-! ## A node with nothing new to hand out (2026-10-10)

`HasReady` returning `false` (`RawNode.HasReady.spec`) leaves the node as `ownRawNodeIdle`:
`ownRawNode` at a state with no queued message, no unstable entry still to be handed out,
and so the lower bounds `outlb` and `unst` at their least (`ownRawNodeIdle_facts`). Its use:
`node.go`'s `run` keeps a `Ready` it computed earlier armed when `HasReady` is `false`,
and may send it; by the lower bounds that `Ready` held nothing but committed entries still
the next ones, and possibly a stale `SoftState`/`HardState` (which only reset what
`HasReady` compares against), and `ownRawNodeIdle_ready` turns the node back into
`ownRawNodeReady` for it, so that `acceptReady` takes it. -/

/-- See the section header. -/
def ownRawNodeIdle (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) : IProp GF :=
  iprop(∃ (s : NState) (ps : PState) (rnv : RawNode) (sv : SoftState)
      (steps : List raftpb.Message),
  "Hrn" ∷ rawNodeOwn rn rnv ∗
  "Hphys" ∷ ownRaftPhys γ.reCfg rnv.raft' id s ∗
  "Hghost" ∷ ownRaftGhost γ id ps ∗
  "%Hrel" ∷ ⌜NStateRel s ps⌝ ∗
  "%Hin" ∷ ⌜id ∈ γ.reCfg⌝ ∗
  "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps ∗
  "Hsteps_cap" ∷ ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) ∗
  "#Hpend" ∷ ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingRel γ id m p) ∗
  "Hpown" ∷ ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingOwn m p) ∗
  "#Hdeliv" ∷ isCommitted γ rs.delivered ∗
  "#Hstrecs" ∷ storedRecs γ s.logst.prev s.logst.stored ∗
  "%Hdlen" ∷ ⌜rs.delivered.length = (uint.Z s.logst.applying).toNat⌝ ∗
  "%Hunp" ∷ ⌜rs.unpersisted = s.logst.unpersisted⌝ ∗
  "%Hsnap" ∷ ⌜s.logst.snap = none⌝ ∗
  "%Hstok" ∷ ⌜StepsOk s rs.steps⌝ ∗
  "%Htrm" ∷ ⌜rs.term = s.term⌝ ∗
  "%Hstor" ∷ ⌜rs.storage = s.logst.storage⌝ ∗
  "%Hpvoff" ∷ ⌜s.prevote = false⌝ ∗
  "%Hrs_out" ∷ ⌜rs.outlb = s.gh.outlb⌝ ∗
  "%Hrs_unst" ∷ ⌜rs.unst = s.gh.unst⌝ ∗
  "%Hrs_clb" ∷ ⌜uint.Z rs.clb ≤ uint.Z s.logst.committed⌝ ∗
  -- nothing new: no queued message, no unstable entry still to be handed out
  "%Hidle" ∷ ⌜s.gh.outlb = 0 ∧ nextUnstable s.logst = []⌝)

theorem ownRawNodeIdle_intro (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s : NState) (ps : PState) (rnv : RawNode) (sv : SoftState) (steps : List raftpb.Message)
    (Hrel : NStateRel s ps) (Hin : id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : s.prevote = false) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hidle : s.gh.outlb = 0 ∧ nextUnstable s.logst = []) :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhys γ.reCfg rnv.raft' id s -∗ ownRaftGhost (GF := GF) γ id ps -∗
      rnv.prevSoftSt' ↦□ sv -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) -∗
      ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingRel γ id m p) -∗
      ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingOwn m p) -∗
      isCommitted γ rs.delivered -∗
      storedRecs γ s.logst.prev s.logst.stored -∗
      ownRawNodeIdle γ rn id rs := by
  iintro Hrn Hphys Hghost #Hsoft Hsteps Hcap #Hpend Hpown #Hdeliv #Hstrecs
  unfold ownRawNodeIdle
  iexists s, ps, rnv, sv, steps
  simp only [named]
  iframe Hrn Hphys Hghost Hsoft Hsteps Hcap Hpend Hpown Hdeliv Hstrecs
  ipureintro
  exact ⟨Hrel, Hin, Hasync, Hdlen, Hunp, Hsnap, Hstok, Htrm, Hstor, Hpvoff, Hrs_out, Hrs_unst,
    Hrs_clb, Hidle⟩

theorem ownRawNodeIdle_ownRawNode (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNodeIdle (GF := GF) γ rn id rs -∗ ownRawNode γ rn id rs := by
  iintro H
  iNamed H
  iapply ownRawNode_intro γ rn id rs s ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap Hstok
    Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

/-- What the client sees of an idle node: the lower bounds at their least, and the commit
index at most the committed log handed out (`applying`). -/
theorem ownRawNodeIdle_facts (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNodeIdle (GF := GF) γ rn id rs -∗
      ⌜rs.outlb = 0 ∧ rs.unst = false⌝ ∗ ownRawNodeIdle γ rn id rs := by
  iintro H
  iNamed H
  icases ownRaftPhys_gh γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hgh, Hphys⟩
  isplitr
  · ipureintro
    refine ⟨Hrs_out.trans Hidle.1, ?_⟩
    rw [Hrs_unst]
    cases Hu : s.gh.unst
    · rfl
    · rcases Hgh Hu with H | H
      · exact absurd Hidle.2 H
      · exact absurd Hsnap H
  iapply ownRawNodeIdle_intro γ rn id rs s ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hidle
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

/-- Accepting, after all, a `Ready` computed earlier and abandoned (see the section
header): an idle node (no `Ready` outstanding: `rs.steps = []`, `rs.unpersisted = []`) is
`ownRawNodeReady` for a `Ready` `rd` that hands out no messages and no entries, whose
committed entries `ce` extend the committed log handed out and are the next ones up to
the commit index's lower bound (`ownRawNodeReady_abandon`'s third fact), and whose soft
state, snapshot and read states are as `readyWithoutAccept` leaves them. -/
theorem ownRawNodeIdle_ready (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready)
    (ce : List raftpb.Entry)
    (Hsteps0 : rs.steps = []) (Hunp0 : rs.unpersisted = [])
    (Hrdz : rd.Snapshot' = zero_val raftpb.Snapshot ∧ rd.ReadStates' = slice.nil)
    (Hce_ok : ∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z rs.clb ∧
      uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int)) :
    ⊢ (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) -∗
      rd.CommittedEntries' ↦*□ ce -∗
      ownSliceCap raftpb.Entry rd.CommittedEntries' (DFrac.own 1) -∗
      isCommitted γ (rs.delivered ++ ce) -∗
      ownRawNodeIdle (GF := GF) γ rn id rs -∗ ownRawNodeReady γ rn id rs rd ce [] [] := by
  iintro #Hrdsoft #Hce Hce_cap #Hcommitted H
  iNamed H
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hpend
  have Hsteps_nil : steps = [] := by
    rw [Hsteps0] at Hlen; exact List.eq_nil_of_length_eq_zero Hlen
  subst Hsteps_nil
  icases ownRaftPhys_view γ.reCfg rnv.raft' id s $$ Hphys with
    ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  iunfold ownRawNodeReady
  iexists s, ps, rnv, sv
  simp only [named]
  iframe Hrn Hghost Hsoft Hsteps Hsteps_cap Hcommitted Hstrecs Hrdsoft Hce Hce_cap
  isplitl
  · iunfold ownRaftPhysReady
    iexists rss, sl1, sl2, ms1, ms2
    simp only [named]
    iframe Hf_id Hf_Term Hf_Vote Hf_readStates Hf_raftLog Hf_state Hf_lead Hf_msgs Hf_msgsAA
      HmsgsAA HmsgsAA_cap Houtbox Hlog
    isplitr
    · ipureintro; exact Hrs
    isplitr
    · ipureintro; exact HmsgsAA_ok
    isplitr
    · ipureintro; exact Hout_term
    isplitr
    · ipureintro; exact Hgh_out
    isplitr
    · ipureintro; exact Hgh_unst
    isplitr
    · ipureintro; simp
    isplitl [Hmsgs Hmsgs_cap]
    · iintro - -
      iframe Hmsgs Hmsgs_cap
    iintro %sl1' %sl2' %ms1' %ms2' %o %ls' %g HfTerm HfVote Hfrs Hflog Hfst Hfld Hfm Hm Hmc Hfma
      Hma Hmac #Hob %H1 %H2 %H3 %H4 Hl
    iapply Hclose $$ %sl1' %sl2' %ms1' %ms2' %o %ls' %g HfTerm HfVote Hfrs Hflog Hfst Hfld Hfm
      Hm Hmc Hfma Hma Hmac Hob %H1 %H2 %H3 %H4 Hl
  ipureintro
  refine ⟨Hrel, Hin, Hasync, Hdlen, Hunp0 ▸ Hunp.symm, Hsnap, Htrm, Hstor, Hpvoff, Hrs_out, Hrs_unst, Hrs_clb, Hrdz,
    fun e He => ?_, Hidle.2.symm⟩
  obtain ⟨H1, H2⟩ := Hce_ok e He
  have Hne : ce ≠ [] := by intro h; subst h; simp at He
  have : 0 < ce.length := List.length_pos_iff.2 Hne
  have := uint_Z_nonneg s.logst.applying
  refine ⟨by omega, by omega, by omega⟩

end rawnodeReady

end EtcdGrove
end Perennial
