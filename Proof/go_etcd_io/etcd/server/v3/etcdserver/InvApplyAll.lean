/-
The apply loop's step `applyAll` (`server.go`: a batch from raft applied, the applied index's
waiters triggered, the snapshot trigger): the shared vocabulary of the specs of `applyAll`,
`applySnapshot`, `Backend`, `snapshotIfNeededAndCompactRaftLog`, `shouldSnapshotToDisk`,
`shouldSnapshotToMemory` and the trust-boundary contracts `snapshot`, `compactRaftLog`,
`createMergedSnapshotMessage`, `sendMergedSnap`. Lean-first (no Rocq counterpart); the request
path's unit 4b (2026-10-13).

**The server, as `applyAll` sees it** (`isServerApplyAll s γr`, persistent, beside the apply
thread's `isServer`): the applied index's waiters (`applyWait`, a `WaitTime` for
`appliedAtLeast γr`, `isWaitTime`), the raft wrapper's `msgSnapC` (a bag channel of messages:
`applyAll` only passes a received one to the merged-snapshot contract), the configuration's
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

/-- `s.bemu`'s lock invariant at fraction `q`: `s.be`. -/
def bemuP (s : Loc) (q : Qp) : IProp GF :=
  iprop(∃ b : GoInterface, srvBeAddr s ↦{DFrac.own q} b)

/-- **A reader slot of `s.bemu`** (the apply thread's, for `Backend`). -/
def srvBemuReader (s : Loc) : IProp GF :=
  sync.ownRWMutex (srvBemuAddr s) (bemuP s)

/-- **The server, as `applyAll` sees it** (persistent; see the file header). -/
def isServerApplyAll (s : Loc) (γr : ReadNames) : IProp GF :=
  iprop(∃ (wt : GoInterface) (msc : Loc) (sc : w64),
    srvApplyWaitAddr s ↦□ wt ∗ isWaitTime wt (appliedAtLeast γr) ∗
    rnMsgSnapCAddr (srvRAddr s) ↦□ msc ∗
    (∃ (γc : ChanNames) (P : Loc → IProp GF), isChanBag γc msc (V := Loc) P) ∗
    srvCfgFieldAddr s go!"SnapshotCount" ↦□ sc)

instance isServerApplyAll_persistent (s : Loc) (γr : ReadNames) :
    Persistent (isServerApplyAll (GF := GF) s γr) := by
  unfold isServerApplyAll; infer_instance

/-- **The apply thread's snapshot state** (see the file header). -/
def srvSnapState (s ep : Loc) : IProp GF :=
  iprop(∃ (d m : w64) (f : Bool), epDiskSnapAddr ep ↦ d ∗ epMemSnapAddr ep ↦ m ∗
    srvForceSnapAddr s ↦ f)

/-- **The apply thread's resources besides the KV and the snapshot state** at the applied index
`ai` with the protocol's state `st` (what `applyEntries` takes and gives back): `ep`'s applied
index, term and conf state, the protocol, the backend, the applying index, the logger's reader
slot, the ghost applied index's half. -/
def srvApplyRes (s ep : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) : IProp GF :=
  iprop(epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfStateAddr ep ↦ cs ∗
    applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗
    srvAppliedOwn γr ai)

end defs

end EtcdGrove
end Perennial
