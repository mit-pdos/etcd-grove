/-
`fileutil.ReadDir(d, opts...)` (read_dir.go): applies the options (`WithExt`, `fileutil.withExtFn`:
the last one's extension wins), opens `d` (`os.Open`), reads every name (`Readdirnames(-1)`),
closes it (deferred), sorts the names (`sort.Strings`) and, with an extension, keeps the names
whose `filepath.Ext` is it. The WAL's calls: `readWALNames` (no option) and `wal.Exist`
(`WithExt(".wal")`).

Over the part's shared-mode directory specs (`os.Open.wp_dirS`, `File.Readdirnames.wp_dirS`,
`File.Close.wp_dirS`): `d` the directory `j` (`osPathS`), a fraction of a claim on names `N` of
`j` (`osNames`, unchanged). On success the names read, `names`, are `Readdirnames`'s (valid; a name
of `N` is among them iff `j` has it, at most once) and the result is `fileutil.ReadDirOut names ext`
(sorted, filtered by the extension); on an error nothing. The option slice and its closures are
given back. Proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/ReadDir.lean`.
Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.WithExt
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.PkgInit
public import LinuxFs.Proof.path.filepath.Model
public import LinuxFs.Proof.os.NsS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

/-- The extension the options leave (the last one's; none: `""`). -/
def fileutil.optsExt (es : List GoString) : GoString := es.foldl (fun _ e => e) ""

/-- `ReadDir`'s result from the names read and the extension: the names sorted, then, with an
extension, those of that extension. -/
def fileutil.ReadDirOut (names : List GoString) (ext : GoString) (rs : List GoString) : Prop :=
  ∃ srt : List GoString, names.Perm srt ∧
    (∀ (i j : Nat) (xi xj : GoString), srt[i]? = some xi → srt[j]? = some xj → i < j →
      go.GoStringLe xi xj) ∧
    rs = if ext = "" then srt else srt.filter (fun v => decide (filepath.extModel v = ext))

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.spec : Prop :=
  ∀ (d : GoString) (sl : GoSlice) (gs : List GoFunc) (es : List GoString) (dqs : DFrac) (R : Roots)
    (j : Ino) (dq : DFrac) (qc : Qp) (N : NameSet) (dqn : DFrac) (h : NamesH),
  es.length = gs.length →
  {{ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      osPathS (GF := GF) R d dq j ∗ osCallPerm (GF := GF) qc ∗ osNames (GF := GF) j N dqn h ∗
      sl ↦*{dqs} gs ∗ [∗list] i ↦ g ∈ gs, fileutil.withExtFn (GF := GF) g (es.getD i "") }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir)) (Val #d)) (Val #sl))
  {{ (r : GoSlice) (err : GoInterface), RET (PairV #r #err); osPathS R d dq j ∗ osCallPerm qc ∗
      osNames j N dqn h ∗ sl ↦*{dqs} gs ∗
      ((∃ names rs : List GoString, ⌜err = interface.nil ∧ (∀ b ∈ names, NameOk b) ∧
            (∀ b, N.Mem b → ((h.cur !! b).isSome ↔ b ∈ names)) ∧
            (∀ b, N.Mem b → names.count b ≤ 1) ∧ fileutil.ReadDirOut names (fileutil.optsExt es) rs⌝ ∗
          r ↦* rs) ∨
       ⌜err ≠ interface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
