/-
`fileutil.ReadDir(d/b, opts...)` (read_dir.go) of a name `b` holding nothing (a fraction of a claim of
`d`'s directory `j` on names containing it), with any options (`WithExt`'s): `os.Open` fails, and the
error comes back, a `*PathError` of a nonzero errno that is `ENOENT` when the file system does not fail
on `d/b` (`FsNoErrAt`: `NoIoErr`'s `PathErrno`, its `open` case, the user's approval of 2026-11-23;
`os.Open.wp_absentErrSW`, `Proof/os/OpenAbsentNE.lean`). What `wal.Exist` of an absent WAL directory
needs to answer `false` (claim #34). Proved in
`Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/ReadDirAbsentErr.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir
public import Proof.os.OpenAbsentNE

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
abbrev fileutil.ReadDir.specAbsentErr : Prop :=
  ∀ (d b : GoString) (sl : GoSlice) (gs : List GoFunc) (es : List GoString) (dqs : DFrac) (R : Roots)
    (j : Ino) (dq : DFrac) (qc : Qp) (N : NameSet) (dqn : DFrac) (h : NamesH),
  es.length = gs.length → NameOk b → N.Mem b → h.cur !! b = none →
  {{ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      osPathS (GF := GF) R d dq j ∗ osCallPerm (GF := GF) (callKey R d) qc ∗ osNames (GF := GF) j N dqn h ∗
      sl ↦*{dqs} gs ∗ [∗list] i ↦ g ∈ gs, fileutil.withExtFn (GF := GF) g (es.getD i "") }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir)) (Val #(child d b))) (Val #sl))
  {{ (r : GoSlice) (err : GoInterface), RET (PairV #r #err); osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      osNames j N dqn h ∗ sl ↦*{dqs} gs ∗ ⌜err ≠ interface.nil⌝ ∗
      ∃ e : w64, ⌜e ≠ 0 ∧ (FsNoErrAt (child d b) → e = ENOENT)⌝ ∗ os.errnoPathErr err e }}

end spec

end EtcdGrove
end Perennial

end
