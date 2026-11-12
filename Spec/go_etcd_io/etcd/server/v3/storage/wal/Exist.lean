/-
`wal.Exist` (WAL W4a, 2026-11-11, revised after the Freeze review and its second round; the approved W4 Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision") Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code at the etcd pin `c90b03b56` (S/ = `server/storage/wal/`) under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester under the crash harness (`notes/decisions.md`, "WAL W3"). An axiomatized body is read as one that performs the abstract-disk extension's steps (`AbsDiskStep`): the step each spec's atomic update or post names.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Spec.go_uber_org.zap.Defs
public import Proof.go_etcd_io.raft.v3.InvPbLog
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [walpb_sem : go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

/-- **`Exist(dir)`** (S/util.go:30-42, with the fork's fix `c90b03b56`): whether `dir` holds `.wal`
entries. Under the area discipline (`walAreaOk`, `walAreaDir`) only a WAL's own segment files are
such entries: `Create` renames a directory holding its first segment into place, and a WAL
disappears only by a crash before its name is durable (`walCrash`) or, after an I/O failure in
`Create` (`¬ storage.walCreateOk`), by `cleanupWAL`'s rename to `dir.broken.*`. `Exist` returns false only when
`ReadDir` succeeds with no `.wal` entry or the directory does not exist; any other `ReadDir` failure
gives true (the fix: nonissue `etcd-wal-exist-readdir-error-removes-wal`). So false means no WAL;
true claims nothing (the reads after it fail when there is none). -/
abbrev wal.Exist.spec : Prop :=
  ∀ (r dir : GoString) (o : Option WalDur), walAreaDir r dir →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ walAreaOk r ∗ walDirIs dir o }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Exist)) (Val #dir))
  {{ (b : Bool), RET #b; walDirIs dir o ∗ ⌜b = false → o = none⌝ }}

end spec

end EtcdGrove
end Perennial
