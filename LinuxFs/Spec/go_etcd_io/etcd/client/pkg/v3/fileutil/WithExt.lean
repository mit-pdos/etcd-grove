/-
`fileutil.WithExt(ext)` (read_dir.go): a `ReadDirOption`, the closure that sets a `*ReadDirOp`'s
`ext` to `ext` (`fileutil.withExtFn`, persistent: the closure reads only its captured copy of
`ext`). Proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/WithExt.lean`. Lean-first.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.os.Base

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

/-- `g` is a `ReadDirOption` setting the option's `ext` to `ext`. -/
def fileutil.withExtFn (g : GoFunc) (ext : GoString) : IProp GF :=
  iprop(□ ∀ (op : Loc) (o : go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirOp) (Φ : val → IProp GF),
    op ↦ o -∗ ▷ (op ↦ go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirOp.mk ext -∗ Φ #()) -∗
      WP (App (Val #g) (Val #op)) {{ Φ }})

instance fileutil.withExtFn_persistent (g : GoFunc) (ext : GoString) :
    Persistent (fileutil.withExtFn (GF := GF) g ext) := by
  unfold fileutil.withExtFn; infer_instance

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.WithExt.spec : Prop :=
  ∀ (ext : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.WithExt)) (Val #ext))
  {{ (g : GoFunc), RET #g; fileutil.withExtFn g ext }}

end spec

end EtcdGrove
end Perennial
