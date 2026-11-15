/-
`fileutil.TouchDirAll(lg, d)` (WAL W4a, 2026-11-11, revised after the Freeze review and its second round; the approved W4
Draft's §1.4 and the revision design, `notes/decisions.md`, "WAL W4a" and "WAL W4a revision"). Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code
at the etcd pin `c90b03b56` (`client/pkg/fileutil/fileutil.go:49-85`, with F-N2 and F-N4's part 1)
under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester
under the crash harness (`notes/decisions.md`, "WAL W3"). The body is read as one that performs the
abstract-disk extension's `"DirDurable"` step.
-/
module

public import GooseLang.Ext.AbsDisk.Specs
public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import Spec.go_uber_org.zap.Defs
public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **`TouchDirAll(lg, d)`**, `d` a single path element `name` under the durable directory `parent`, a
clean absolute path, and `d` not under the WAL area `r` (only the WAL's functions create there):
creates `d` if it is missing (`MkdirAll`), and fsyncs its parent whether or not it created it
(F-N2, F-N4's part 1), so on success `d`'s entry and its ancestors' are durable (`dirDurable`).
Its whole footprint: `d` and its missing ancestors (created), the parents' fsyncs, and the probe
`d/.touch` that `IsDirWriteable` writes and then removes (fileutil.go:36-45, :88), so an existing
file of that name is overwritten and deleted. No WAL directory is ever `d/.touch` (its name has a
`.`, `walAreaDir`, and `d` is not under the area), and no durable name is while the area is reserved
(`walAreaOk r` carries durable's reservation, whose names never hide: `durableNameOk`), which is why
the spec takes `walAreaOk r` (revision round 2, B2; Go test `rev2-tests` `TestRev2TouchProbe`).
(No package-initialization premise: `fileutil`'s initializer sets only its lock functions and
`ErrLocked`, which `TouchDirAll` does not read; the package is outside `etc/gen-init.py`'s closure
until W4c.) -/
abbrev fileutil.TouchDirAll.spec : Prop :=
  ∀ (lg : Loc) (r d parent name : GoString),
  d = parent ++ go!"/" ++ name → pathElemOk name → cleanAbsPath parent → ¬ underDir r d →
  {{ zapLoggerOk (GF := GF) lg ∗ walAreaOk r ∗ dirDurable parent }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll)) (Val #lg)) (Val #d))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ -∗ dirDurable d }}

end spec

end EtcdGrove
end Perennial
