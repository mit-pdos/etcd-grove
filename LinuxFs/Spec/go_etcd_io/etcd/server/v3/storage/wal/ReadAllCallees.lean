/-
**The callees of `ReadAll`'s switch arms with no spec** (W3/W5 of `notes/wal-fsext-plan.md`, nineteenth
session; S/wal.go:523-596): hypotheses of `WAL.ReadAll.wp_proof`, over the unmarshalling `U`
(`WalUnmarshal`, `WalEncFold.lean`: `U.Ok Mr` is the round trip the fold needs) and the client's raft
messages `P` (`WalPbIn`), as `WalPbIn.MarshalEntLaw` is of `saveEntry`'s (the part cannot import the
main tree's raftpb/pbutil specs, plan §10; to discharge with the client instance at C6). Each is true
of the Go code: `MustUnmarshalEntry`/`MustUnmarshalState` (decoder.go:215-225) are
`pbutil.MustUnmarshal` into a fresh message, which panics only on bytes `proto.Unmarshal` rejects
(here: `U` decodes them), and the getters read the fields.

The hard state `ReadAll` builds is written after it is read (`state.Reset()` on the error arms), so
it is held through an owned predicate `HsO` (`WalHsOwn`), frozen into `P.hsIn` (persistent) only on
success, as `WalPbIn.ZeroLaw` freezes a fresh zero one. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalEncFold
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.PbSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **`MustUnmarshalEntry(d)` of bytes `U` decodes** (S/wal.go:525): a fresh entry holding the decoded
entry; the bytes are only read. -/
abbrev WalPbIn.UnmarshalEntLaw (P : WalPbIn GF) (U : WalUnmarshal) : Prop :=
  ∀ (d : GoSlice) (dq : DFrac) (bs : List w8) (e : EntryM), U.decEntry bs = some e →
  {{ d ↦*{dq} bs }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.MustUnmarshalEntry)) (Val #d))
  {{ (l : Loc), RET #l; d ↦*{dq} bs ∗ P.entIn l e }}

/-- **`e.GetTerm()` of an entry** (S/wal.go:537, the error message's): its term. -/
abbrev WalPbIn.GetTermLaw (P : WalPbIn GF) : Prop :=
  ∀ (l : Loc) (e : EntryM),
  {{ P.entIn l e }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftpb.Entry.ty @!! go!"GetTerm")) (Val #()))
  {{ RET #e.Term'; True }}

/-- **The hard states `ReadAll` owns** (see the file header): `HsO p h`, the `*raftpb.HardState` `p`
holds `h`, owned. A fresh zero one is owned (`zero`); `MustUnmarshalState` of bytes `U` decodes returns
one (`unmarshal`, S/wal.go:546); `GetCommit` reads it (:579); `Reset` writes it (the error arms);
it freezes into `P.hsIn` (`freeze`). -/
structure WalHsOwn (P : WalPbIn GF) (U : WalUnmarshal) (HsO : Loc → HardStateM → IProp GF) : Prop where
  zero : ∀ p : Loc, p ↦ (zero_val go_etcd_io.raft.v3.raftpb.HardState) ⊢ HsO p hsZero
  unmarshal : ∀ (d : GoSlice) (dq : DFrac) (bs : List w8) (h : HardStateM), U.decState bs = some h →
    {{ d ↦*{dq} bs }}
      (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.MustUnmarshalState)) (Val #d))
    {{ (p : Loc), RET #p; d ↦*{dq} bs ∗ HsO p h }}
  getCommit : ∀ (p : Loc) (h : HardStateM),
    {{ HsO p h }}
      (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.raftpb.HardState.ty @!! go!"GetCommit"))
        (Val #()))
    {{ RET #h.Commit'; HsO p h }}
  reset : ∀ (p : Loc) (h : HardStateM),
    {{ HsO p h }}
      (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.raftpb.HardState.ty @!! go!"Reset"))
        (Val #()))
    {{ RET #(); HsO p hsZero }}
  freeze : ∀ (p : Loc) (h : HardStateM) (E : CoPset), HsO p h ⊢ |={E}=> P.hsIn p h

/-- **`proto.Clone(state).(*raftpb.HardState)`** (S/wal.go:648): a fresh hard state holding the same. -/
abbrev WalPbIn.CloneHsLaw (P : WalPbIn GF) : Prop :=
  ∀ (p : Loc) (h : HardStateM),
  {{ P.hsIn p h }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.HardState.ty) #p)))
  {{ (m : GoInterface), RET #m; ∃ p' : Loc,
      ⌜m = interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.HardState.ty) #p'⌝ ∗
      P.hsIn p' h }}

/-- **`pbutil.MustUnmarshalMessage(&snap, d)` into a fresh `walpb.Snapshot`, of bytes `U` decodes**
(S/wal.go:568): the snapshot holds the decoded index and term, read-only from then on. -/
abbrev go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage.specWalSnap (U : WalUnmarshal) : Prop :=
  ∀ (sp : Loc) (d : GoSlice) (dq : DFrac) (bs : List w8) (s : w64 × w64), U.decSnap bs = some s →
  {{ (sp ↦ (zero_val go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot) : IProp GF) ∗ d ↦*{dq} bs }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.ty) #sp)))
      (Val #d))
  {{ RET #(); d ↦*{dq} bs ∗ walSnapIdTerm sp s }}

/-- **`snap.GetTerm()`** (S/wal.go:573): the term (as `Snapshot.GetIndex.spec` the index). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetTerm.spec : Prop :=
  ∀ (sp : Loc) (s : w64 × w64),
  {{ walSnapIdTerm (GF := GF) sp s }}
    (App (Val (sp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.ty @!! go!"GetTerm")) (Val #()))
  {{ RET #s.2; True }}

end spec

end EtcdGrove
end Perennial
