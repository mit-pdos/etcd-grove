/-
`fileutil.TouchDirAll(lg, d)` over `fsExt` (W4/W13 of `notes/wal-fsext-plan.md`; the main tree's axiom
`Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/TouchDirAll.lean` restated over the tree's shared mode).
FU/ = `client/pkg/fileutil/fileutil.go` at the pin (F-N2: the parent's fsync in both branches). To be
proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/TouchDirAll.lean`. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import Spec.go_uber_org.zap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **`TouchDirAll(lg, d)`** (FU/fileutil.go:49-85), `d = parent/name`, `parent` a clean absolute path
(the roots `R` hold `/`, so every ancestor `TouchDirAll`'s `Exist` loop may climb to has a spine, a
prefix of `parent`'s), `name` an element. The caller holds a fraction of `parent`'s spine, the whole
of `name` and of everything under it (`osSubtreeH`: `MkdirAll` creates `d` if missing; the probe
`d/.touch`, written and removed by `IsDirWriteable`, is under it), and the whole call permission
(`mkdir` is a directory operation). On success `name` holds a directory and every entry that wrote
`name` is committed (`osCommitLb`: the parent's fsync, in both branches, F-N2), so `d`'s entry
survives any crash once `parent`'s does (the old spec's `dirDurable d`, which the WAL layer derives
from it). -/
abbrev fileutil.TouchDirAll.spec : Prop :=
  ∀ (lg : Loc) (R : Roots) (j0 jp : Ino) (d parent name : GoString) (qp : Qp) (h : NamesH),
  d = parent ++ go!"/" ++ name → pathElemOk name → cleanAbsPath parent → (go!"/", j0) ∈ R →
  {{ zapLoggerOk (GF := GF) lg ∗ osInv ∗ osSharedInv R ∗ osPathS R parent (DFrac.own qp) jp ∗
      osCallPerm 1 ∗ osSubtreeH jp name h }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll)) (Val #lg)) (Val #d))
  {{ (err : GoInterface), RET #err; osPathS R parent (DFrac.own qp) jp ∗ osCallPerm 1 ∗
      ∃ h', osSubtreeH jp name h' ∗
        (⌜err = interface.nil⌝ -∗ ∃ (J : Ino) (n : Nat),
          ⌜h'.cur !! name = some (.dir J) ∧ h'.next ≤ n⌝ ∗ osCommitLb n) }}

end spec

end EtcdGrove
end Perennial
