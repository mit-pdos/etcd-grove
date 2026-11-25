/-
`fileutil.RemoveMatchFile(lg, dir, matchFunc)` (`client/pkg/fileutil/fileutil.go:176-205` at the etcd
pin `edc800c6f`) **on an empty directory**: `Exist(dir)` (`os.Stat`), `ReadDir(dir)`, then
`os.Remove(dir/name)` for every name `matchFunc` accepts, collecting the failures. Of an empty
directory `ReadDir` reads no name, so `matchFunc` is never called and nothing is removed: the
directory's claims come back unchanged. The error (`Exist` false: `fmt.Errorf`; `ReadDir`'s) is
unconstrained, which is all `bootstrapSnapshot` needs (it only logs it, `bootstrap.go:223-254`).

Over the part's shared-mode directory specs (as `ReadDir.spec`): `dir` the directory `j` (`osPathS`),
the whole claim on its names (`.except []`) at some fraction, holding nothing (`h.cur` empty). The
logger is a zap logger (`zapLoggerOk`, so Go's `zap.NewNop()` branch for nil is not taken). Claim #34,
stage 4 (2026-11-23). Proved in `Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/RemoveMatchFile.lean`.
Lean-first.
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.PkgInit
public import Proof.os.SharedAu
public import Spec.go_uber_org.zap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.RemoveMatchFile.spec : Prop :=
  ∀ (lg : Loc) (d : GoString) (mf : GoFunc) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp)
    (dqn : DFrac) (h : NamesH),
  (∀ b, h.cur !! b = none) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗ zapLoggerOk lg ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗
      osPathS (GF := GF) R d dq j ∗ osCallPerm (GF := GF) (callKey R d) qc ∗
      osNames (GF := GF) j (.except []) dqn h }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.RemoveMatchFile)) (Val #lg))
      (Val #d)) (Val #mf))
  {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      osNames j (.except []) dqn h }}

end spec

end EtcdGrove
end Perennial
