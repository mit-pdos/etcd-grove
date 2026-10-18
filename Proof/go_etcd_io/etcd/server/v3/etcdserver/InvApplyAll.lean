/-
The apply loop's step `applyAll` (`server.go`: a batch from raft applied, the applied index's
waiters triggered, the snapshot trigger): the shared vocabulary of the specs of `applyAll`,
`applySnapshot`, `Backend`, `snapshotIfNeededAndCompactRaftLog`, `shouldSnapshotToDisk`,
`shouldSnapshotToMemory` and the trust-boundary contracts `snapshot`, `compactRaftLog` (until
D19p, 2026-10-18, also `createMergedSnapshotMessage`, `sendMergedSnap`). Lean-first (no Rocq counterpart); the request
path's unit 4b (2026-10-13).

**The server, as `applyAll` sees it** (`isServerApplyAll s γr`, persistent, beside the apply
thread's `isServer`): the applied index's waiters (`applyWait`, a `WaitTime` for
`appliedAtLeast γr`, `isWaitTime`), the raft wrapper's `msgSnapC` (a bag channel of messages,
which never delivers since D19p, 2026-10-18: a one-member cluster's raft sends no `MsgSnap`; until
then `applyAll` passed a received one to the merged-snapshot contract), the configuration's
`SnapshotCount`.

**The apply thread's own snapshot state** (`srvSnapState s ep`): `ep.diskSnapshotIndex`,
`ep.memorySnapshotIndex`, `s.forceDiskSnapshot` (the apply thread's: `ForceSnapshot` is called by
the apply package, `snapshot` resets it), and a reader slot of `s.bemu` (`Backend` read-locks it;
`applySnapshot`, the writer, does not run: raft's contract hands over no snapshot).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

abbrev srvBemuAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"bemu" s
abbrev srvBeAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"be" s
abbrev srvForceSnapAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"forceDiskSnapshot" s
abbrev epDiskSnapAddr (ep : Loc) : Loc := structFieldRef etcdProgress go!"diskSnapshotIndex" ep
abbrev epMemSnapAddr (ep : Loc) : Loc := structFieldRef etcdProgress go!"memorySnapshotIndex" ep
abbrev taSnapshotAddr (ta : Loc) : Loc := structFieldRef toApply go!"snapshot" ta
abbrev taNotifycAddr (ta : Loc) : Loc := structFieldRef toApply go!"notifyc" ta

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `s.bemu`'s lock invariant at fraction `q`: `s.be`, at half the fraction (D19i part 2: the
other half of the field is `↦□`, `NewServer`'s, so the backend `s.be` holds is known for good;
`InvStorageVersion.lean`). -/
def bemuP (s : Loc) (q : Qp) : IProp GF :=
  iprop(∃ b : GoInterface, srvBeAddr s ↦{DFrac.own q.half} b)

/-- **A reader slot of `s.bemu`** (the apply thread's, for `Backend`). -/
def srvBemuReader (s : Loc) : IProp GF :=
  sync.ownRWMutex (srvBemuAddr s) (bemuP s)

/-- **The server, as `applyAll` sees it** (persistent; see the file header). -/
def isServerApplyAll (s : Loc) (γr : ReadNames) : IProp GF :=
  iprop(∃ (wt : GoInterface) (msc : Loc) (sc : w64),
    srvApplyWaitAddr s ↦□ wt ∗ isWaitTime wt (appliedAtLeast γr) ∗
    rnMsgSnapCAddr (srvRAddr s) ↦□ msc ∗
    (∃ (γc : ChanNames) (P : Loc → IProp GF), isChanBag γc msc (V := Loc) P ∗
      -- (D19p, 2026-10-18) it never delivers: a one-member cluster's raft sends no `MsgSnap`
      □ (∀ m : Loc, P m -∗ False)) ∗
    srvCfgFieldAddr s go!"SnapshotCount" ↦□ sc ∗
    -- (D19i part 1) `s.stopping`, which `applyAll` selects on beside `raftAdvancedC`
    (∃ stg : Loc, srvStoppingAddr s ↦□ stg ∗ stopChan stg))

instance isServerApplyAll_persistent (s : Loc) (γr : ReadNames) :
    Persistent (isServerApplyAll (GF := GF) s γr) := by
  unfold isServerApplyAll; infer_instance

/-- **The apply thread's snapshot state** (see the file header) at the applied index `ai`: the
snapshot indices at most `ai`; and (D19i part 1, 2026-10-18) the raft wrapper's `MemoryStorage`
`ms` and the application's snapshot token (`memSnapTok`), its compaction boundary at most `ai`,
its snapshot index at least `sl` (`snapshot` raises it to `ai`, which `compactRaftLog` then
compacts below). -/
def srvSnapState (s ep ms : Loc) (γs : MemStorNames) (ai sl : w64) : IProp GF :=
  iprop(∃ (d m : w64) (f : Bool), epDiskSnapAddr ep ↦ d ∗ epMemSnapAddr ep ↦ m ∗
    srvForceSnapAddr s ↦ f ∗ ⌜uint.Z d ≤ uint.Z ai ∧ uint.Z m ≤ uint.Z ai⌝ ∗
    rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗
    ∃ σ : StorState, memSnapTok ms γs σ ∗
      ⌜uint.Z σ.prev.index' ≤ uint.Z ai ∧ uint.Z sl ≤ uint.Z σ.ss.index'⌝)

/-- **The apply thread's resources besides the KV and the snapshot state** at the applied index
`ai` with the protocol's state `st` (what `applyEntries` takes and gives back): `ep`'s applied
index, term and conf state, the protocol, the backend, the applying index, the logger's reader
slot, the ghost applied index's half. -/
def srvApplyRes (s ep : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) : IProp GF :=
  iprop(epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
    applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗
    srvAppliedOwn γr ai)

end defs

end EtcdGrove
end Perennial
