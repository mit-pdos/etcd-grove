/-
`w.sync()` and `w.saveState(s)` **before a rename** (W2 of `notes/wal-fsext-plan.md`, "W2 implementation
log", fourth session): `cut` (S/wal.go:875-965) writes the new segment's headers into `N.tmp`, a file the
program owns wholly (no WAL layout tracks it before the rename), on its own `w`: several locks (the old
segments' then `N.tmp`'s), `dirFile`, `fp` and `state` set. These generalize W4's pre-rename specs
(`WAL__SaveSnapshotPre.lean`, `Create`'s `w`: one lock, no `dirFile`/`fp`/`state`):

* `walPreInL`: W4's `walPreIn` with the locks any list ending with the tail's (`ls ++ [lt]`, `w.tail()`); the
  fields `sync` and `SaveSnapshot` do not read (`dirFile`, `fp`, `state`, `decoder`, ...) are the
  caller's frame. `walPreIn` is its instance at `ls = []` (`walPreIn_L`, the proof file), and W4's
  `WAL.sync.specPre` a corollary of `WAL.sync.specPreL` (`WAL.sync.specPre_of_L`).
* `WAL.saveState.specPre`: over the two fields it touches (`state`, `encoder`) and any guarded writer
  (`io.writerStreamP`, as `encoder.encode.specG`): `cut` instantiates it with `os.File.writerStream`
  (`io.writerStream_P`).
* The laws of the raft messages `saveState` reads (`WalPbIn.IsEmptyLaw`, `WalPbIn.MarshalHsLaw`): the
  part cannot import the main tree's specs of `raft.IsEmptyHardState`/`pbutil.MustMarshalMessage`
  over `hsRO` (plan §10, the raft-root clash), so the proofs take them over the client's `P.hsIn`.

Proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/WAL__cutPre.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshotPre
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **A `w` before a rename, its tail the locked file `lt` (of `f`)** (see the file header): the
fields `sync`/`SaveSnapshot` read, the locks `ls ++ [lt]` (the old segments', then the tail's). -/
def walPreInL (w lg : Loc) (dir : GoString) (mds : GoSlice) (md : List w8) (e : Loc) (ls : List Loc)
    (lt f : Loc) (snapi enti : w64) : IProp GF :=
  iprop(∃ locks : GoSlice,
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"metadata" w ↦ mds ∗ mds ↦*□ md ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
      (BI.pure True : IProp GF) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"enti" w ↦ enti ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapi" w ↦ snapi ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗ ⌜e ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
    locks ↦* (ls ++ [lt]) ∗ ownSliceCap Loc locks (DFrac.own 1) ∗ fileutil.lockedFile lt f)

/-- **`w.sync()` before a rename** (S/wal.go:967-992): W4's `WAL.sync.specPre` over `walPreInL` (any
locks, the tail last). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPreL : Prop :=
  ∀ (w lg : Loc) (dir : GoString) (mds : GoSlice) (md : List w8) (e : Loc) (ls : List Loc)
    (lt f : Loc) (snapi enti : w64)
    (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF) (S : List w8 → IProp GF)
    (lim : Nat) (out pend : List w8) (c : w32),
  out.length + pend.length ≤ lim → walPreSyncOk f W S →
  ⊢ io.writerStream (wal.fileWi f) lim W B -∗
    {{ encEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗
        walPreInL w lg dir mds md e ls lt f snapi enti ∗ ownEncoder e (wal.fileWi f) c pend ∗ W out }}
      (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
        go!"sync")) (Val #()))
    {{ (err : GoInterface), RET #err;
        walPreInL w lg dir mds md e ls lt f snapi enti ∗ ownEncoder e (wal.fileWi f) c [] ∗
        ((⌜err = GoInterface.nil⌝ ∗ S (out ++ pend)) ∨
         (⌜err ≠ GoInterface.nil⌝ ∗ (B out pend ∨ W (out ++ pend)))) }}

/-- **`raft.IsEmptyHardState` over the client's hard states**: whether `hp` holds an empty state
(`hsEmptyP`; a nil `hp` holds the zero state, empty). -/
abbrev WalPbIn.IsEmptyLaw (P : WalPbIn GF) : Prop :=
  ∀ (hp : Loc) (hs : HardStateM),
  {{ P.hsIn hp hs }}
    (App (Val (@! go_etcd_io.raft.v3.IsEmptyHardState)) (Val #hp))
  {{ (b : Bool), RET #b; ⌜b = true ↔ hsEmptyP hs⌝ }}

/-- **`pbutil.MustMarshalMessage` of a non-empty hard state**: a fresh non-nil slice of its encoding
(`Mr.encState`, the bytes the WAL's state record holds). -/
abbrev WalPbIn.MarshalHsLaw (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (hp : Loc) (hs : HardStateM), ¬ hsEmptyP hs →
  {{ P.hsIn hp hs }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.HardState.ty) #hp)))
  {{ (d : GoSlice), RET #d; d ↦* Mr.encState hs ∗ ⌜d ≠ slice.nil⌝ }}

/-- The frame of the state record of `hs`, the chain's CRC before it `c`. -/
def stateFrame (Mr : WalMarshal) (c : w32) (hs : HardStateM) : List w8 :=
  frame (walRecEnc ⟨stateType, hash.crc32.crc32c c (Mr.encState hs), Mr.encState hs⟩)

/-- **`w.saveState(hp)` before a rename** (S/wal.go:1083-1091), over any guarded writer: of an empty
hard state, nothing; else `w.state := hp` and `hp`'s state record encoded after what the encoder
holds (the post of `encoder.encode.specG`). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.specPre (P : WalPbIn GF)
    (Mr : WalMarshal) : Prop :=
  ∀ (w e : Loc) (sp0 hp : Loc) (hs : HardStateM) (wi : GoInterfaceOk) (W : List w8 → IProp GF)
    (B : List w8 → List w8 → IProp GF) (ok : List w8 → Prop) (out pend : List w8) (c : w32),
  (∀ xs ys, xs <+: ys → ok ys → ok xs) →
  (¬ hsEmptyP hs → ok (out ++ pend ++ stateFrame Mr c hs) ∧
    recSize (recOf ⟨stateType, hash.crc32.crc32c c (Mr.encState hs), Mr.encState hs⟩) < 2 ^ 47) →
  ⊢ io.writerStreamP wi ok W B -∗
    {{ encEnv ∗ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ sp0 ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
        ownEncoder e wi c pend ∗ W out ∗ P.hsIn hp hs }}
      (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
        go!"saveState")) (Val #hp))
    {{ (err : GoInterface), RET #err;
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
        ((⌜err = GoInterface.nil ∧ hsEmptyP hs⌝ ∗
            structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ sp0 ∗
            ownEncoder e wi c pend ∗ W out) ∨
         (⌜¬ hsEmptyP hs⌝ ∗
            structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ hp ∗
            ∃ pend' : List w8,
            ownEncoder e wi (hash.crc32.crc32c c (Mr.encState hs)) pend' ∗
            ((∃ ys : List w8, ⌜err = GoInterface.nil ∧ ys ++ pend' = pend ++ stateFrame Mr c hs⌝ ∗
                W (out ++ ys)) ∨
             (∃ a b : List w8, ⌜err ≠ GoInterface.nil ∧ pend' = [] ∧
                a ++ b <+: pend ++ stateFrame Mr c hs⌝ ∗ B (out ++ a) b)))) }}

end spec

end EtcdGrove
end Perennial
