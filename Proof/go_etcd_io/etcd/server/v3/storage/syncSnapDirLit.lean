/-
`syncSnapDir`'s function literal (`server/storage/backend.go`, etcd PR #22499, branch
`pr-verify/etcd-22499`):

```go
var syncSnapDir = func(dir string) error {
	d, err := fileutil.OpenDir(dir)
	if err != nil {
		return err
	}
	defer d.Close()
	return fileutil.Fsync(d)
}
```

The literal, `syncSnapDir.lit` (`Fs.lean`), is what the package variable holds (the package
fact, `storageInit`); `syncSnapDir.wp_lit` proves that it syncs a directory (`syncSnapDirFn`).
The proof is that of etcd PR #22518's function `syncSnapDir` (branch `pr-verify/etcd-22518`,
`Proof/.../storage/syncSnapDir.lean`), whose body is the same: Goose translates the literal to
the same expression as that function's `impl`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvSnapshotBackend
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync
public import Spec.os.File__Close

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **The function value `f` syncs a directory** (persistently: it may be called any number of
times): `f(dir)`, with a rename of `src` onto `dst` in `dir` pending, returns `nil` once the
rename's directory entry is durable, or an error (whose `Error()` returns a string), after which
nothing is known of the rename (still pending if the directory could not be opened, unknown if
the sync failed). What #22518's `storage.syncSnapDir.spec` says of its function `syncSnapDir`, said of a
value. -/
def syncSnapDirFn (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (dir src dst : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
        fs.renamePending src dst ∗ ⌜fs.dirOf dst = dir⌝ }}
      (App (Val #f) (Val #dir))
    {{ (err : GoInterface), RET #err; fsResult err (fs.entryDurable src dst) iprop(True) }})

instance syncSnapDirFn_persistent (f : GoFunc) : Persistent (syncSnapDirFn (GF := GF) f) := by
  unfold syncSnapDirFn; infer_instance

theorem syncSnapDir.wp_lit
    (wp_OpenDir : fileutil.OpenDir.spec (GF := GF) (hG := hG))
    (wp_Fsync : fileutil.Fsync.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) :
    ⊢ syncSnapDirFn (GF := GF) syncSnapDir.lit := by
  unfold syncSnapDirFn
  imodintro
  iintro %dir %src %dst
  wp_start as ⟨Hpend, %Hdir⟩
  unfold syncSnapDir.lit syncSnapDir.litBody
  wp_apply wp_with_defer as %defer defer
  wp_apply wp_OpenDir as %f %err Hres
  unfold fsResult
  icases Hres with (⟨%Herr, Hh⟩ | ⟨%e, %Herr, #He, -⟩)
  · subst Herr
    wp_auto
    wp_apply wp_Fsync $$ [$Hh $Hpend] as %err2 ⟨Hh, Hres2⟩
    · ipureintro; exact Hdir
    wp_apply wp_Close $$ [$Hh] as %err3 -
    iapply HΦ
    iunfold fsResult at Hres2
    iexact Hres2
  · subst Herr
    wp_auto
    iapply HΦ
    iright
    iexists e
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact He
    itrivial

end defs

end EtcdGrove
end Perennial
