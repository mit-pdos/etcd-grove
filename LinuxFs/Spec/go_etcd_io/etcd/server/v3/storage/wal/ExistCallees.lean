/-
The callee specs `wal.Exist`'s proof takes as hypotheses (W12 of `notes/wal-fsext-plan.md`, the W7-W12
log). None is proved yet.

* **`errIsNotExist err b`**: `errors.Is(err, os.ErrNotExist)` returns `b` (persistent; for any value of
  the `os.ErrNotExist` variable). What `Exist` asks of `ReadDir`'s errors.
* **`fileutil.ReadDir.specAbsentIs`**: `ReadDir.specAbsent` (proved, no option) with `Exist`'s option
  slice, its error answering `errors.Is` with some boolean. The first part is `ReadDir.wp_proofAbsent`
  with `applyOpts` over a slice (as `ReadDir.wp_proof`); the second needs `errors.Is` of a `*PathError`
  of an errno against a pointer error (Perennial's `errors.Is.spec`, with the error tree of the part's
  `os` errors, which no spec gives yet: `notes/perennial-changes.md`, as `errors.IsErrno.spec`).
* **`fileutil.ReadDir.specChildIs`**: `ReadDir.spec` of `d/b` holding the directory `J` (the read path
  through a fraction of a claim of `d`'s directory on names holding `b`, as `ReadDir.specAbsent`'s, not a
  spine to `d/b`: the program holds half of the area claim, which cannot be split into the `.only [b]`
  claim a spine needs), its error answering `errors.Is(_, os.ErrNotExist)` with `false`. Provable since
  the semantics' `ENOENT` rule (2026-11-14, pending the user's review: `ENOENT` from `open` only for a
  path that does not resolve, from `getdents` only for a removed directory): the `os` layer is proved
  (`LinuxFs/Proof/os/NsChildS.lean`: `os.Open.wp_dirChildS`, `os.File.Readdirnames.wp_dirChildS`, over
  the extension's `wp_osOpenDirChildS`/`wp_osDirReadNextChildS`; errors `os.errnoPathErr err e`,
  `e ≠ ENOENT`). Left: `ReadDir`'s own loops (`applyOpts`, the filter; `sort.Strings` needs at most
  `2^62` names, which nothing bounds: `ReadDir.wp_proof` is `sorry` for the same reasons) and
  `errors.IsPathErrnoNotExist.spec` below.
* **`errors.IsPathErrnoNotExist.spec`**: `errors.Is(err, os.ErrNotExist)` of a `*PathError` of a nonzero
  errno `e` answers `e = ENOENT`. True in Go (`errors.Is` unwraps the `*PathError` to the `Errno`, whose
  `Is` compares the target with `oserror.ErrNotExist`); its proof needs the error tree of the part's `os`
  errors (Perennial's `errors.Is.spec` with `syscall.Errno.Is`, `notes/perennial-changes.md`, as
  `errors.IsErrno.spec`) and `os`'s package fact to say `os.ErrNotExist` is `oserror.ErrNotExist`, distinct
  from `ErrPermission`, `ErrExist` and `errors.ErrUnsupported` (it says only "some error"). Not proved.
Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir
public import LinuxFs.Proof.os.NsChildS
public import LinuxFs.Proof.os.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`errors.Is(err, os.ErrNotExist)` returns `b`** (persistent). -/
def errIsNotExist (err : GoInterface) (b : Bool) : IProp GF :=
  iprop(□ ∀ (t : GoInterface) (Φ : val → IProp GF),
    typedPointsto (globalAddr os.ErrNotExist) t DFrac.discard -∗ ▷ Φ #b -∗
      WP (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #t)) {{ Φ }})

instance errIsNotExist_persistent (err : GoInterface) (b : Bool) :
    Persistent (errIsNotExist (GF := GF) err b) := by
  unfold errIsNotExist; infer_instance

/-- See the file header. -/
abbrev errors.IsPathErrnoNotExist.spec : Prop :=
  ∀ (err : GoInterface) (e : w64), e ≠ 0 →
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.os -∗ os.errnoPathErr (GF := GF) err e -∗
      errIsNotExist (GF := GF) err (decide (e = Fs.ENOENT))

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- See the file header. -/
abbrev fileutil.ReadDir.specAbsentIs : Prop :=
  ∀ (d b : GoString) (sl : GoSlice) (gs : List GoFunc) (es : List GoString) (dqs : DFrac) (R : Roots)
    (j : Ino) (dq : DFrac) (qc : Qp) (N : NameSet) (dqn : DFrac) (h : NamesH),
  es.length = gs.length → NameOk b → N.Mem b → h.cur !! b = none →
  {{ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      osPathS (GF := GF) R d dq j ∗ osCallPerm (GF := GF) qc ∗ osNames (GF := GF) j N dqn h ∗
      sl ↦*{dqs} gs ∗ [∗list] i ↦ g ∈ gs, fileutil.withExtFn (GF := GF) g (es.getD i "") }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir)) (Val #(child d b))) (Val #sl))
  {{ (r : GoSlice) (err : GoInterface), RET (PairV #r #err); osPathS R d dq j ∗ osCallPerm qc ∗
      osNames j N dqn h ∗ sl ↦*{dqs} gs ∗ ⌜err ≠ interface.nil⌝ ∗ ∃ bn : Bool, errIsNotExist err bn }}

/-- See the file header. -/
abbrev fileutil.ReadDir.specChildIs : Prop :=
  ∀ (d b : GoString) (sl : GoSlice) (gs : List GoFunc) (es : List GoString) (dqs : DFrac) (R : Roots)
    (jp : Ino) (dq : DFrac) (Np : NameSet) (dqp : DFrac) (hp : NamesH) (J : Ino) (qc : Qp)
    (N : NameSet) (dqn : DFrac) (h : NamesH),
  es.length = gs.length → NameOk b → Np.Mem b → hp.cur !! b = some (.dir J) →
  {{ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      osPathS (GF := GF) R d dq jp ∗ osNames (GF := GF) jp Np dqp hp ∗ osCallPerm (GF := GF) qc ∗
      osNames (GF := GF) J N dqn h ∗
      sl ↦*{dqs} gs ∗ [∗list] i ↦ g ∈ gs, fileutil.withExtFn (GF := GF) g (es.getD i "") }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir)) (Val #(child d b))) (Val #sl))
  {{ (r : GoSlice) (err : GoInterface), RET (PairV #r #err); osPathS R d dq jp ∗ osNames jp Np dqp hp ∗
      osCallPerm qc ∗ osNames J N dqn h ∗ sl ↦*{dqs} gs ∗
      ((∃ names rs : List GoString, ⌜err = interface.nil ∧ (∀ b ∈ names, NameOk b) ∧
            (∀ b, N.Mem b → ((h.cur !! b).isSome ↔ b ∈ names)) ∧
            (∀ b, N.Mem b → names.count b ≤ 1) ∧ fileutil.ReadDirOut names (fileutil.optsExt es) rs⌝ ∗
          r ↦* rs) ∨
       ⌜err ≠ interface.nil⌝ ∗ errIsNotExist err false) }}

end spec

end EtcdGrove
end Perennial
