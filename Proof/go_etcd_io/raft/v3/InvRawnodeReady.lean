/-
**A `Ready` computed but not yet accepted (2026-10-10)**

`node.go`'s `run` does not call `RawNode.Ready`: it calls its two halves,
`readyWithoutAccept` (when `HasReady`), hands the `Ready` to the application
(`readyc <- rd`), and only then `acceptReady(rd)`, with no raft step in between.
`ownRawNodeReady γ rn id rs rd ce es` is the node between the two: `ownRawNode γ rn id rs`
with the outbox `r.msgs`' slice given up to `rd.Messages` (`readyWithoutAccept` builds
`rd.Messages` in place from `r.msgs`, and `acceptReady` only sets the field to `nil`), and
what `acceptReady` reads of `rd` recorded: the soft state pointer read-only (or `nil`), no
snapshot, the read states (2026-10-13: below), the committed entries `ce` (read-only, with the slice's capacity,
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

**Read states (2026-10-13).** `readyWithoutAccept` sets `rd.ReadStates = r.readStates`
when it is not empty, and `acceptReady` sets `r.readStates = nil` when `rd.ReadStates` is
not empty. The slice is read-only in the struct (`ownRaftMisc`), so `readyWithoutAccept`
hands out `rd.ReadStates ↦*□ sts` and each `ReadState`'s `readStateOk`, persistent facts
it copies out of the ghost state (`ownRaftGhost_readStates`) without a model step: nothing
has to be given back when the `Ready` is abandoned, and a stale `Ready` that `node.go`
sends later still carries them. `acceptReady` takes the model step `Step.takeReads`
(the protocol state's `ReadState`s become `[]`, as the struct's do); what it needs of `rd`
is that an empty `rd.ReadStates` means the node has no `ReadState` (`Hrdrs`): true of a
fresh `Ready` (the slice is the node's when non-empty) and of an idle node (`HasReady`
is `false` only when `r.readStates` is empty, `ownRawNodeIdle`).

**Read credits (2026-10-13).** Each `MsgReadIndex` in the abstract outbox carries a read
credit (`ownRaftGhost`'s `rdOwn`), and `Ready` hands each one out with its message, for the
transport to pass to the receiver's `Step`. The credits come out of the ghost state with
the drain of the abstract outbox (`ownRaftGhost_drain`), which `ownRawNodeReady_handout`
takes -- where the `Ready` is handed out (`node.go`: in the atomic update of `readyc <- rd`)
-- rather than `acceptReady`: `ownRawNodeReady … true`'s ghost state is at the drained
outbox, while the struct's queues are emptied only by `acceptReady`. So
`ownRawNodeReady` records, of the outbox `readyWithoutAccept` found, that its messages were
legitimately sent (`Hout`, which `acceptReady` needs of the self-addressed responses it
queues) and that the messages handed out hold at most as many `MsgReadIndex`s as it had
credits for (`Hrdc`: `rdCountM ms ≤ rdCount ps.outbox`, from `outboxRel`: a physical
message is a `MsgReadIndex` iff its abstraction is a `readIndex`, `msgAbs_rdCount`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode
-- `ownRaftGhost_drain` (2026-10-13)
public import Proof.go_etcd_io.raft.v3.Protocol.Refinement

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
    (ms : List raftpb.Message) (h : Bool) : IProp GF :=
  iprop(∃ (rsl sl1 sl2 : GoSlice) (ms1 ms2 : List raftpb.Message),
    "#Hf_id" ∷ r.[raft, go!"id"] ↦□ id ∗
    "Hf_Term" ∷ r.[raft, go!"Term"] ↦ s.term ∗
    "Hf_Vote" ∷ r.[raft, go!"Vote"] ↦ s.vote ∗
    "Hf_readStates" ∷ r.[raft, go!"readStates"] ↦ rsl ∗
    "#HreadStates" ∷ rsl ↦*□ s.rd.states ∗
    "HreadStates_cap" ∷ ownSliceCap ReadState rsl (DFrac.own 1) ∗
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
    -- the log, after the storage's hand-out if `h` (2026-10-10, `ownRaftLog_handout`)
    "Hlog" ∷ ownRaftLog s.log (if h then logHanded s.logst else s.logst) ∗
    "Hclose" ∷ (∀ (sl1' sl2' : GoSlice) (ms1' ms2' : List raftpb.Message) (o : List Msg)
                  (ls' : LogState) (g : NGhost) (rs' : GoSlice) (rd' : RdState),
        r.[raft, go!"Term"] ↦ s.term -∗
        r.[raft, go!"Vote"] ↦ s.vote -∗
        r.[raft, go!"readStates"] ↦ rs' -∗
        rs' ↦*□ rd'.states -∗ ownSliceCap ReadState rs' (DFrac.own 1) -∗
        ⌜rd'.ro = s.rd.ro ∧ rd'.pend = s.rd.pend⌝ -∗
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
        ownRaftPhys cfg r id { s with outbox := o, logst := ls', gh := g, rd := rd' }))

/-! ### Read credits (see the file header) -/

/-- The number of `MsgReadIndex`s among physical messages. -/
def rdCountM (ms : List raftpb.Message) : Nat :=
  ms.countP (fun m => decide (m.Type' = MsgReadIndex))

theorem rdCountM_cons (m : raftpb.Message) (ms : List raftpb.Message) :
    rdCountM (m :: ms) = (if m.Type' = MsgReadIndex then 1 else 0) + rdCountM ms := by
  unfold rdCountM
  rw [List.countP_cons]
  by_cases h : m.Type' = MsgReadIndex <;> simp [h, Nat.add_comm]

theorem mtypeOf_MsgReadIndex : mtypeOf MsgReadIndex = some .readIndex := rfl

/-- Only `MsgReadIndex` is abstracted as a `readIndex`. -/
theorem mtypeOf_readIndex (t : w32) (H : mtypeOf t = some .readIndex) : t = MsgReadIndex := by
  unfold mtypeOf at H
  split at H <;> simp_all
  rename_i h
  exact uint_Z_inj.1 (by rw [h]; rfl)

/-- A queued message contributes a read-index request to the abstract outbox iff it is a
`MsgReadIndex`. -/
theorem msgAbs_rdCount (m : raftpb.Message) (a : Option Msg) :
    msgAbs (GF := GF) m a ⊢ ⌜rdCount a.toList = if m.Type' = MsgReadIndex then 1 else 0⌝ := by
  iintro H
  unfold msgAbs
  icases H with (%H | ⟨%ty, %ents, %ctx, %H, -, -⟩ | ⟨%sv, %voters, %H, -, -⟩)
  · obtain ⟨Hn, rfl⟩ := H
    have Hne : m.Type' ≠ MsgReadIndex := (mtypeOf_None_ne _ Hn).2.2.2.2.2.2.2.2.1
    ipureintro
    simp [rdCount, Hne]
  · obtain ⟨H1, -, rfl⟩ := H
    ipureintro
    simp only [Option.toList_some, rdCount_singleton, absMsg, absMsgFrom]
    by_cases hty : ty = .readIndex
    · subst hty
      simp [mtypeOf_readIndex _ H1]
    · have Hne : m.Type' ≠ MsgReadIndex := by
        intro h
        rw [h, mtypeOf_MsgReadIndex] at H1
        cases H1
        exact hty rfl
      simp [hty, Hne]
  · obtain ⟨H1, rfl⟩ := H
    have Hne : m.Type' ≠ MsgReadIndex := by
      intro h
      rw [h, mtypeOf_MsgReadIndex] at H1
      cases H1
    ipureintro
    simp [rdCount, absSnap, absSnapFrom, Hne]

theorem msgsAbs_rdCount (ms : List raftpb.Message) (as_ : List (Option Msg)) :
    ([∗list] _k ↦ m;a ∈ ms;as_, msgAbs (GF := GF) m a) ⊢
      ⌜rdCountM ms = rdCount (absList as_)⌝ := by
  induction ms generalizing as_ with
  | nil =>
    iintro H
    ihave %Hl := BigSepL2.bigSepL2_length $$ H
    cases as_ with
    | nil => ipureintro; rfl
    | cons _ _ => simp at Hl
  | cons m ms IH =>
    iintro H
    icases (BigSepL2.bigSepL2_cons_inv_left).1 $$ H with ⟨%a, %as', %Has, Hm, H⟩
    subst Has
    ihave %H1 := msgAbs_rdCount m a $$ Hm
    ihave %H2 := IH as' $$ H
    ipureintro
    have Hab : absList (a :: as') = a.toList ++ absList as' := by cases a <;> rfl
    rw [Hab, rdCount_append, H1, ← H2, rdCountM_cons]

/-- `rdCountM ms` credits are one per `MsgReadIndex` of `ms`. -/
theorem rdCred_msgs (γ : RaftNames) (ms : List raftpb.Message) :
    rdCred (GF := GF) γ (rdCountM ms) ⊢
      [∗list] m ∈ ms, rdCred γ (if m.Type' = MsgReadIndex then 1 else 0) := by
  induction ms with
  | nil => iintro _; iempintro
  | cons m ms IH =>
    iintro H
    rw [rdCountM_cons]
    icases (rdCred_split γ _ _).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexact H1
    · iapply IH $$ H2

/-- The node between `readyWithoutAccept` and `acceptReady` (see the file header): the
conjuncts of `ownRawNode γ rn id rs` at a state `s` with an empty queue and nothing
unpersisted (`Ready`'s premises), the struct open without the outbox's contents
(`ownRaftPhysReady`), and what `acceptReady` reads of `rd`: `rd.SoftState` `nil` or
read-only, no snapshot, the read states (if none, the node has none: `Hrdrs`), the
committed entries `ce` extending
`rs.delivered` (`isCommitted`) and the next ones after `applying` (`CeOk`), with their
slice's capacity, and the entries `es` handed out (`nextUnstable`). `ms` are the messages
handed out in `rd.Messages`, which `ownRawNodeReady_abandon` takes back (2026-10-10). Since
2026-10-13 (read credits, see the file header): once handed out (`h`), the ghost state is
at the drained outbox; the outbox's messages were legitimately sent (`Hout`), and `ms`
holds at most as many `MsgReadIndex`s as it has requests (`Hrdc`). -/
def ownRawNodeReady (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready)
    (ce es : List raftpb.Entry) (ms : List raftpb.Message) (h : Bool := false) : IProp GF :=
  iprop(∃ (s : NState) (ps : PState) (rnv : RawNode) (sv : SoftState),
  "Hrn" ∷ rawNodeOwn rn rnv ∗
  "Hphys" ∷ ownRaftPhysReady γ.reCfg rnv.raft' id s rd.Messages' ms h ∗
  "Hghost" ∷ ownRaftGhost γ id (if h then { ps with outbox := [] } else ps) ∗
  "#Hout" ∷ ([∗list] x ∈ ps.outbox, isMessage γ x) ∗
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
  "%Hrdz" ∷ ⌜rd.Snapshot' = zero_val raftpb.Snapshot⌝ ∗
  "#Hrdrs" ∷ (∃ sts : List ReadState, rd.ReadStates' ↦*□ sts ∗ ⌜sts = [] → s.rd.states = []⌝) ∗
  "#Hce" ∷ rd.CommittedEntries' ↦*□ ce ∗
  "Hce_cap" ∷ ownSliceCap raftpb.Entry rd.CommittedEntries' (DFrac.own 1) ∗
  "%Hceok" ∷ ⌜CeOk s.logst ce⌝ ∗
  "%Hes" ∷ ⌜es = nextUnstable s.logst⌝ ∗
  "%Hrdc" ∷ ⌜rdCountM ms ≤ rdCount ps.outbox⌝)

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
  simp only [Bool.false_eq_true, ↓reduceIte]
  let g : NGhost := { outlb := ms1.length + ms2.length,
                      unst := decide (nextUnstable s.logst ≠ []) }
  ihave Hphys := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst %g %rsl %s.rd Hf_Term Hf_Vote
    Hf_readStates HreadStates HreadStates_cap %(And.intro rfl rfl)
    Hf_raftLog Hf_state Hf_lead Hf_msgs Hm1 Hc1 Hf_msgsAA HmsgsAA HmsgsAA_cap
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

/-- The storage's hand-out for the entries a computed `Ready` hands out (2026-10-10): the
right to append them, ahead of `acceptReady` (`ownRaftLog_handout`). `node.go` runs it in
the atomic update of `readyc <- rd`, giving the right to the application with the `Ready`;
`acceptReady` takes the node after it. Since 2026-10-13 also the drain of the abstract
outbox (`Step.drain`, `ownRaftGhost_drain`), handing out with each message its read credit
(one for a `MsgReadIndex`). -/
theorem ownRawNodeReady_handout (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List raftpb.Entry) (ms : List raftpb.Message) :
    ⊢ ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms false ==∗
      ownRawNodeReady γ rn id rs rd ce es ms true ∗ appendRight rs.storage es ∗
      [∗list] m ∈ ms, rdCred γ (if m.Type' = MsgReadIndex then 1 else 0) := by
  iintro H
  iunfold ownRawNodeReady at H
  icases H with ⟨%s, %ps, %rnv, %sv, H⟩
  iNamed H
  iunfold ownRaftPhysReady at Hphys
  icases Hphys with ⟨%rsl, %sl1, %sl2, %ms1, %ms2, Hphys⟩
  iNamed Hphys
  simp only [Bool.false_eq_true, ↓reduceIte]
  imod ownRaftLog_handout _ _ Hunp Hsnap $$ Hlog with ⟨Hlog, Happ⟩
  imod ownRaftGhost_drain γ id ps [] List.nil_subperm $$ Hghost with ⟨Hghost, Hcr⟩
  rw [show rdCount ps.outbox - rdCount ([] : List Msg) =
      rdCountM ms + (rdCount ps.outbox - rdCountM ms) by
    rw [show rdCount ([] : List Msg) = 0 from rfl]; omega]
  icases (rdCred_split γ _ _).1 $$ Hcr with ⟨Hcr, -⟩
  imodintro
  isplitr [Happ Hcr]
  · iunfold ownRawNodeReady
    iexists s, ps, rnv, sv
    simp only [named, ↓reduceIte]
    iframe Hrn Hghost Hout Hsoft Hsteps Hsteps_cap Hcommitted Hstrecs Hrdsoft Hrdrs Hce Hce_cap
    isplitl
    · iunfold ownRaftPhysReady
      iexists rsl, sl1, sl2, ms1, ms2
      simp only [named, ↓reduceIte]
      iframe Hf_id Hf_Term Hf_Vote Hf_readStates HreadStates HreadStates_cap Hf_raftLog
        Hf_state Hf_lead Hf_msgs Hf_msgsAA HmsgsAA HmsgsAA_cap Houtbox Hundo Hlog Hclose
      ipureintro
      exact ⟨HmsgsAA_ok, Hout_term, Hgh_out, Hgh_unst, Hmslen⟩
    ipureintro
    exact ⟨Hrel, Hin, Hasync, Hdlen, Hunp, Hsnap, Htrm, Hstor, Hpvoff, Hrs_out, Hrs_unst,
      Hrs_clb, Hrdz, Hceok, Hes, Hrdc⟩
  isplitl [Happ]
  · rw [Hes, ← Hstor]; iexact Happ
  iapply rdCred_msgs γ ms $$ Hcr

/-! ## A node with nothing new to hand out (2026-10-10)

`HasReady` returning `false` (`RawNode.HasReady.spec`) leaves the node as `ownRawNodeIdle`:
`ownRawNode` at a state with no queued message, no unstable entry still to be handed out,
no `ReadState` (2026-10-13), and so the lower bounds `outlb` and `unst` at their least (`ownRawNodeIdle_facts`). Its use:
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
  -- nothing new: no queued message, no unstable entry still to be handed out, no
  -- `ReadState` (2026-10-13)
  "%Hidle" ∷ ⌜s.gh.outlb = 0 ∧ nextUnstable s.logst = [] ∧ s.rd.states = []⌝)

theorem ownRawNodeIdle_intro (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s : NState) (ps : PState) (rnv : RawNode) (sv : SoftState) (steps : List raftpb.Message)
    (Hrel : NStateRel s ps) (Hin : id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : s.prevote = false) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hidle : s.gh.outlb = 0 ∧ nextUnstable s.logst = [] ∧ s.rd.states = []) :
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
      · exact absurd Hidle.2.1 H
      · exact absurd Hsnap H
  iapply ownRawNodeIdle_intro γ rn id rs s ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hidle
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

/-- Accepting, after all, a `Ready` computed earlier and abandoned (see the section
header): an idle node (no `Ready` outstanding: `rs.steps = []`, `rs.unpersisted = []`) is
`ownRawNodeReady` for a `Ready` `rd` that hands out no messages and no entries, whose
committed entries `ce` extend the committed log handed out and are the next ones up to
the commit index's lower bound (`ownRawNodeReady_abandon`'s third fact), and whose soft
state and snapshot are as `readyWithoutAccept` leaves them; its read states `sts` may be
any (2026-10-13): the idle node has none, which is all `acceptReady` needs. -/
theorem ownRawNodeIdle_ready (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready)
    (ce : List raftpb.Entry) (sts : List ReadState)
    (Hsteps0 : rs.steps = []) (Hunp0 : rs.unpersisted = [])
    (Hrdz : rd.Snapshot' = zero_val raftpb.Snapshot)
    (Hce_ok : ∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z rs.clb ∧
      uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int)) :
    ⊢ (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) -∗
      rd.CommittedEntries' ↦*□ ce -∗
      ownSliceCap raftpb.Entry rd.CommittedEntries' (DFrac.own 1) -∗
      isCommitted γ (rs.delivered ++ ce) -∗ rd.ReadStates' ↦*□ sts -∗
      ownRawNodeIdle (GF := GF) γ rn id rs -∗ ownRawNodeReady γ rn id rs rd ce [] [] false := by
  iintro #Hrdsoft #Hce Hce_cap #Hcommitted #Hrsts H
  iNamed H
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hpend
  have Hsteps_nil : steps = [] := by
    rw [Hsteps0] at Hlen; exact List.eq_nil_of_length_eq_zero Hlen
  subst Hsteps_nil
  icases ownRaftPhys_view γ.reCfg rnv.raft' id s $$ Hphys with
    ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  ihave #Hout := ownRaftGhost_outbox _ _ _ $$ Hghost
  ihave #Hrdrs : iprop(∃ sts : List ReadState, rd.ReadStates' ↦*□ sts ∗
      ⌜sts = [] → s.rd.states = []⌝) $$ []
  · iexists sts
    iframe Hrsts
    ipureintro; intro _; exact Hidle.2.2
  iunfold ownRawNodeReady
  iexists s, ps, rnv, sv
  simp only [named, Bool.false_eq_true, ↓reduceIte]
  iframe Hrn Hghost Hout Hsoft Hsteps Hsteps_cap Hcommitted Hstrecs Hrdsoft Hrdrs Hce Hce_cap
  isplitl
  · iunfold ownRaftPhysReady
    iexists rss, sl1, sl2, ms1, ms2
    simp only [named, Bool.false_eq_true, ↓reduceIte]
    iframe Hf_id Hf_Term Hf_Vote Hf_readStates HreadStates HreadStates_cap Hf_raftLog Hf_state
      Hf_lead Hf_msgs Hf_msgsAA HmsgsAA HmsgsAA_cap Houtbox Hlog
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
    iintro %sl1' %sl2' %ms1' %ms2' %o %ls' %g %rs' %rd' HfTerm HfVote Hfrs Hrs' Hrsc %Hrd'
      Hflog Hfst Hfld Hfm Hm Hmc Hfma Hma Hmac #Hob %H1 %H2 %H3 %H4 Hl
    iapply Hclose $$ %sl1' %sl2' %ms1' %ms2' %o %ls' %g %rs' %rd' HfTerm HfVote Hfrs Hrs' Hrsc
      %Hrd' Hflog Hfst Hfld Hfm Hm Hmc Hfma Hma Hmac Hob %H1 %H2 %H3 %H4 Hl
  ipureintro
  refine ⟨Hrel, Hin, Hasync, Hdlen, Hunp0 ▸ Hunp.symm, Hsnap, Htrm, Hstor, Hpvoff, Hrs_out, Hrs_unst, Hrs_clb, Hrdz,
    fun e He => ?_, Hidle.2.1.symm, Nat.zero_le _⟩
  obtain ⟨H1, H2⟩ := Hce_ok e He
  have Hne : ce ≠ [] := by intro h; subst h; simp at He
  have : 0 < ce.length := List.length_pos_iff.2 Hne
  have := uint_Z_nonneg s.logst.applying
  refine ⟨by omega, by omega, by omega⟩

/-- The `ReadState`s of the protocol state, each `readStateOk` (2026-10-13): persistent,
copied out of `rdOwn`. -/
theorem ownRaftGhost_readStates (γ : RaftNames) (id : w64) (ps : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id ps -∗ [∗list] st ∈ ps.rd.states, readStateOk γ st := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  iunfold rdOwn at Hrd
  icases Hrd with ⟨%γl, %rqm, -, -, -, -, -, #Hst0, -⟩
  iexact Hst0

/-- **A client's reading of a `ReadState`** (2026-10-13): the client that created the read
context `c` and registered its slice (`isPropData γ rctx c`, as it passed it to
`ReadIndex`) and finds `st`'s `RequestCtx` to be that slice learns `readOk γ c st.Index'`:
its read was created knowing a committed log no longer than the index. (By bytes rather
than by slice: `node_readState_data`.) -/
theorem readStateOk_readOk (γ : RaftNames) (st : ReadState) (c : List w8) :
    ⊢ readStateOk (GF := GF) γ st -∗ isPropData γ st.RequestCtx' c -∗ readOk γ c st.Index' := by
  iintro #Hst #Hpd
  iunfold readStateOk at Hst
  icases Hst with ⟨%c', #Hpd', #Hok⟩
  unfold isPropData
  icases ghostMapElem_agree _ _ _ _ _ _ $$ Hpd Hpd' with %Heq
  subst Heq
  iexact Hok

/-- ... and with `readOk_prefix`: every committed log at least `st.Index'` long extends the
committed log `Lc` the read was created knowing (`readReq γ c Lc`), so applying the log up
to an index of at least `st.Index'` reads a state at least as new as the request. -/
theorem readStateOk_prefix (γ : RaftNames) (st : ReadState) (c : List w8)
    (Lc D : List raftpb.Entry) (Hle : uint.Z st.Index' ≤ (D.length : Int)) :
    ⊢ readStateOk (GF := GF) γ st -∗ isPropData γ st.RequestCtx' c -∗ readReq γ c Lc -∗
      isCommitted γ D -∗ ⌜Lc <+: D⌝ := by
  iintro #Hst #Hpd #Hrq #HD
  ihave #Hok := readStateOk_readOk γ st c $$ Hst Hpd
  iapply readOk_prefix γ c st.Index' Lc D Hle $$ Hok Hrq HD

/-- The physical `ReadState`s are the protocol state's. -/
theorem toPState_rd_states (s : NState) : (toPState s).rd.states = s.rd.states := by
  by_cases h : s.role = .leader <;> simp [toPState, h, rdNL]

end rawnodeReady

end EtcdGrove
end Perennial
