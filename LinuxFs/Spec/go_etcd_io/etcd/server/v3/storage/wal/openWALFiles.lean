/-
`openWALFiles(lg, dirpath, names, nameIndex, write)` (S/wal.go:461-497): opens each of
`names[nameIndex:]` in `dirpath` (write mode: `fileutil.TryLockFile(p, O_RDWR, 0600)`; read mode:
`os.OpenFile(p, O_RDONLY, 0600)`) and wraps it in a `fileutil.FileReader`; on an error closes what
it opened (`closeAll`). At the file-system level, over a fraction of a claim on names `N` of the
directory holding each name as a file (`is`: their inodes, in order; `filepath.Join`'s bound: `|d|` and
each name's length below `2^60`, so that `|d| + |b| + 2 < 2^62`): on success the readers, the
locks (nil in read mode) and each file opened (`walOpenedFile`, fd whole, offset 0); on an error an
error `fmt.Errorf` may wrap. The closer `closeAll` returns is not specified (write mode drops it;
`OpenForRead`'s `Close` needs it, W10). Lean-first; proof `sorry`
(`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/openWALFiles.lean`: needs
`fileutil.TryLockFile`'s spec, `fileutil.NewFileReader`'s, `filepath.Join`'s and `closeAll`'s).
W5 of `notes/wal-fsext-plan.md`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import LinuxFs.Spec.fmt.ErrorfErrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.openWALFiles.spec : Prop :=
  ∀ (lg : Loc) (d : GoString) (sl : GoSlice) (names : List GoString) (dqs : DFrac) (k : w64)
    (write : Bool) (is : List Ino) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) (N : NameSet)
    (dqn : DFrac) (h : NamesH),
  0 ≤ sint.Z k → sint.nat k ≤ names.length → (names.drop (sint.nat k)).length = is.length →
  d.length < 2 ^ 61 →
  (∀ (m : Nat) (b : GoString) (i : Ino), (names.drop (sint.nat k))[m]? = some b → is[m]? = some i →
    N.Mem b ∧ NameOk b ∧ b.length < 2 ^ 60 ∧ h.cur !! b = some (.file i)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R d dq j ∗
      osCallPerm (GF := GF) qc ∗ osNames (GF := GF) j N dqn h ∗ sl ↦*{dqs} names }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.openWALFiles))
      (Val #lg)) (Val #d)) (Val #sl)) (Val #k)) (Val #write))
  {{ (rsl lsl : GoSlice) (cl : GoFunc) (err : GoInterface),
      RET (PairV (PairV (PairV #rsl #lsl) #cl) #err);
      osPathS R d dq j ∗ osCallPerm qc ∗ osNames j N dqn h ∗ sl ↦*{dqs} names ∗
      ((∃ (frs : List GoInterfaceOk) (lfs : List Loc),
          ⌜err = interface.nil ∧ frs.length = is.length ∧ lfs.length = is.length⌝ ∗
          rsl ↦* frs.map GoInterface.ok ∗ ownSliceCap GoInterface rsl (DFrac.own 1) ∗
          lsl ↦* lfs ∗ ownSliceCap Loc lsl (DFrac.own 1) ∗
          [∗list] m ↦ i ∈ is, walOpenedFile write d ((names.drop (sint.nat k)).getD m [])
            i (frs.getD m ⟨go.GoType.PointerType go.string, #()⟩) (lfs.getD m null)) ∨
       ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errOk e) }}

end spec

end EtcdGrove
end Perennial
