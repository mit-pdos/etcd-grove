/-
`readWALNames(lg, dirpath)` (S/util.go:78-88): `fileutil.ReadDir(dirpath)` (no option), then
`checkWALNames`; `ErrFileNotFound` if none is left. Stated at the file-system level, over a fraction of
a claim on names `N` of the directory (`osNames`, as `fileutil.ReadDir`'s): the result is
`WalNamesOut N h`, sorted, non-empty, each a name `parseWALName` may accept, exact on the names of
`N` that parse. For a WAL directory (`walInv`'s `WalDirClaim`, `.except X` with no `.wal` name in
`X`) the names outside `N` are no `.wal` names, so the result is exactly the directory's names that
parse. An error is one `fmt.Errorf` may wrap (`errOk`). Proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/readWALNames.lean`. W5 of
`notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.checkWALNames
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Fs

section pure
variable [GooseExts]

/-- **`readWALNames`' result from a directory whose claim on `N` has the history `h`**: non-empty,
sorted, valid names `parseWALName` may accept, at most once each in `N`; of `N`'s names, only names
the directory has, and every one of them that parses. -/
def WalNamesOut (N : NameSet) (h : NamesH) (ws : List GoString) : Prop :=
  ws ≠ [] ∧ ws.Pairwise go.GoStringLe ∧ (∀ b ∈ ws, NameOk b ∧ walNameMay b) ∧
  (∀ b, N.Mem b → b ∈ ws → (h.cur !! b).isSome) ∧
  (∀ b, N.Mem b → (h.cur !! b).isSome → walNameParses b → b ∈ ws) ∧
  (∀ b, N.Mem b → ws.count b ≤ 1)

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.readWALNames.spec : Prop :=
  ∀ (lg : Loc) (d : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) (N : NameSet)
    (dqn : DFrac) (h : NamesH),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R d dq j ∗
      osCallPerm (GF := GF) qc ∗ osNames (GF := GF) j N dqn h }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.readWALNames)) (Val #lg)) (Val #d))
  {{ (r : GoSlice) (err : GoInterface), RET (PairV #r #err); osPathS R d dq j ∗ osCallPerm qc ∗
      osNames j N dqn h ∗
      ((∃ ws : List GoString, ⌜err = interface.nil ∧ WalNamesOut N h ws⌝ ∗ r ↦* ws) ∨
       ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errOk e) }}

end spec

end EtcdGrove
end Perennial
