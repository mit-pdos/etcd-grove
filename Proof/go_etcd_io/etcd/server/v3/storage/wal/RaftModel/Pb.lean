/-
**The raftpb instance's objects** (W4c U4 b of `notes/wal-fsext-w4c-plan.md`, "W4c U4 log"): the
client's raft messages `P : WalPbIn GF` and the hard states `ReadAll` owns (`HsO`), at the canonical
contents of `RaftModel/Codec.lean` and `RaftModel/EntCodec.lean` (what `walRaftMr` encodes), and the
getters' specs over them.

- `walEntIn l e`: the frozen `*raftpb.Entry` at the canonical content `walEntCanon e` (`entRoC`, the
  registered `raftpb.Entry`'s, part extract `Proof/go_etcd_io/raft/v3/PbContent.lean`), an
  entry below Go's allocation limit (`walEntSmall`).
- `walHsIn p h`: `nil` holding the zero state, or a frozen `*raftpb.HardState` (`hsRoC`: its three
  cells frozen, `hsCells`, and its hidden fields in raft's `protobuf` invariant, `pbMsg`, as raft's
  `hsRO`) at a content of model `h`, the canonical one `walHsCanon h` unless `h` is empty (an empty
  hard state is never marshalled, `saveState`; the tester's `toHS` of a zero state sets the three
  cells, raft's `emptyState` leaves them nil).
- `walHsO p h`: the owned `*raftpb.HardState` at `walHsCanon h`, its hidden fields owned (`hsOwnC`).
- `hsGet p h`: what the getters read (`nil` and the zero state, or frozen cells of model `h`): raft's
  `emptyState` (raft's package fact, `isInitialized`) is one (`rootInit_hsGet`).
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Marshal
public import Proof.go_etcd_io.raft.v3.PbEntryTypeCore
public import Proof.go_etcd_io.raft.v3.Base
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 WalEnc WalFs

section pure
variable [GooseExts]

theorem walHsCanon_term (h : HardStateM) : (walHsCanon h).term.getD (W64 0) = h.Term' :=
  congrArg HardStateM.Term' (walHsCanon_model h)

theorem walHsCanon_vote (h : HardStateM) : (walHsCanon h).vote.getD (W64 0) = h.Vote' :=
  congrArg HardStateM.Vote' (walHsCanon_model h)

theorem walHsCanon_commit (h : HardStateM) : (walHsCanon h).commit.getD (W64 0) = h.Commit' :=
  congrArg HardStateM.Commit' (walHsCanon_model h)

theorem walHsCanon_uf (h : HardStateM) : (walHsCanon h).uf = [] := by
  unfold walHsCanon; split <;> rfl

theorem walHsCanon_zero : walHsCanon hsZero = walHsC0 := by
  unfold walHsCanon; rw [if_pos ⟨rfl, rfl, rfl⟩]

theorem walEntCanon_index (e : EntryM) : (walEntCanon e).index = some e.Index' := rfl

theorem walEntCanon_term (e : EntryM) : (walEntCanon e).term = some e.Term' := rfl

theorem walEntCanon_uf (e : EntryM) : (walEntCanon e).uf = [] := rfl

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A `*raftpb.HardState`'s three cells, frozen, at the content `c` (its hidden fields left out). -/
def hsCells (l : Loc) (c : WalHsC) : IProp GF :=
  iprop(∃ (pt pv pc : Loc), ⌜l ≠ null⌝ ∗
    l.[raftpb.HardState, go!"Term"] ↦□ pt ∗ optCell pt c.term ∗
    l.[raftpb.HardState, go!"Vote"] ↦□ pv ∗ optCell pv c.vote ∗
    l.[raftpb.HardState, go!"Commit"] ↦□ pc ∗ optCell pc c.commit)

instance hsCells_persistent (l : Loc) (c : WalHsC) : Persistent (hsCells (GF := GF) l c) := by
  unfold hsCells; infer_instance

/-- **A frozen `*raftpb.HardState` holding exactly `c`**: its cells, and its hidden fields in the
`protobuf` invariant (raft's `pbMsg`). -/
def hsRoC (l : Loc) (c : WalHsC) : IProp GF :=
  iprop(hsCells l c ∗ pbMsg raftpb.HardState l c.uf)

instance hsRoC_persistent (l : Loc) (c : WalHsC) : Persistent (hsRoC (GF := GF) l c) := by
  unfold hsRoC; infer_instance

/-- A frozen hard state is at a non-nil address (`proto.MarshalPb.spec`'s premise). -/
theorem hsRoC_nonnull (l : Loc) (c : WalHsC) : hsRoC (GF := GF) l c ⊢ ⌜l ≠ null⌝ := by
  unfold hsRoC hsCells
  iintro ⟨⟨%pt, %pv, %pc, %h, -⟩, -⟩
  ipureintro; exact h

/-- **An owned `*raftpb.HardState` holding exactly `c`**, its hidden fields owned. -/
def hsOwnC (l : Loc) (c : WalHsC) : IProp GF :=
  iprop(∃ (pt pv pc : Loc) (st : google_golang_org.protobuf.internal.impl.MessageState) (sc : w32)
      (us : GoSlice), ⌜l ≠ null⌝ ∗
    l.[raftpb.HardState, go!"Term"] ↦ pt ∗ optCell pt c.term ∗
    l.[raftpb.HardState, go!"Vote"] ↦ pv ∗ optCell pv c.vote ∗
    l.[raftpb.HardState, go!"Commit"] ↦ pc ∗ optCell pc c.commit ∗
    l.[raftpb.HardState, go!"state"] ↦ st ∗ l.[raftpb.HardState, go!"sizeCache"] ↦ sc ∗
    l.[raftpb.HardState, go!"unknownFields"] ↦ us ∗ us ↦* c.uf)

/-- **What the getters read of a `*raftpb.HardState`**: `nil` and the zero state, or frozen cells of
model `h`. -/
def hsGet (l : Loc) (h : HardStateM) : IProp GF :=
  iprop(⌜l = null ∧ h = hsZero⌝ ∨ ∃ c : WalHsC, hsCells l c ∗ ⌜c.model = h⌝)

instance hsGet_persistent (l : Loc) (h : HardStateM) : Persistent (hsGet (GF := GF) l h) := by
  unfold hsGet; infer_instance

/-- **The instance's hard states** (`P.hsIn`): `nil` holding the zero state, or a frozen hard state
of model `h`, at the canonical content unless `h` is empty (see the file header). -/
def walHsIn (l : Loc) (h : HardStateM) : IProp GF :=
  iprop(⌜l = null ∧ h = hsZero⌝ ∨
    ∃ c : WalHsC, hsRoC l c ∗ ⌜c.model = h ∧ (hsEmptyP h ∨ c = walHsCanon h)⌝)

instance walHsIn_persistent (l : Loc) (h : HardStateM) : Persistent (walHsIn (GF := GF) l h) := by
  unfold walHsIn; infer_instance

/-- **The instance's entries** (`P.entIn`): a frozen entry at the canonical content, below Go's
allocation limit. -/
def walEntIn (l : Loc) (e : EntryM) : IProp GF :=
  iprop(entRoC l (walEntCanon e) ∗ ⌜walEntSmall e⌝)

instance walEntIn_persistent (l : Loc) (e : EntryM) : Persistent (walEntIn (GF := GF) l e) := by
  unfold walEntIn; infer_instance

/-- **The raftpb instance of the client's raft messages.** -/
def walRaftP : WalPbIn GF where
  hsIn := walHsIn
  entIn := walEntIn
  hsIn_persistent := walHsIn_persistent
  entIn_persistent := walEntIn_persistent

/-- **The hard states `ReadAll` owns** (`HsO`): owned at the canonical content. -/
def walRaftHsO (l : Loc) (h : HardStateM) : IProp GF := hsOwnC l (walHsCanon h)

theorem walHsIn_hsGet (l : Loc) (h : HardStateM) : walHsIn (GF := GF) l h ⊢ hsGet l h := by
  unfold walHsIn hsGet hsRoC
  iintro (%H | ⟨%c, ⟨#Hc, -⟩, %Hm⟩)
  · ileft; ipureintro; exact H
  · iright; iexists c
    iframe Hc
    ipureintro; exact Hm.1

/-- **Raft's `emptyState`** (its package fact) reads as the zero state. -/
theorem rootInit_hsGet :
    go_etcd_io.raft.v3.isInitialized (GF := GF) ⊢
      ∃ es : Loc, (globalAddr emptyState ↦□ es : IProp GF) ∗ hsGet es hsZero := by
  iintro Hi
  unfold go_etcd_io.raft.v3.isInitialized
  iNamed Hi
  icases emptyState with ⟨%es, #Hg, %Hn, #HT, #HV, #HC, -⟩
  iexists es
  iframe Hg
  unfold hsGet
  iright
  iexists walHsC0
  unfold hsCells
  isplitl
  · iexists null, null, null
    iframe HT HV HC
    simp only [walHsC0, optCell]
    ipureintro
    exact ⟨Hn, trivial, trivial, trivial⟩
  · ipureintro; rfl

end defs

end EtcdGrove
end Perennial
