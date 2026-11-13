/-
`fileutil.preallocFixed(f, sizeInBytes)` (preallocate_unix.go): `syscall.Fallocate(fd,
FALLOC_FL_KEEP_SIZE, 0, sizeInBytes)`, `ENOTSUP` (`errors.As`) treated as success: no visible change,
any error. Proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/preallocFixed.lean`.
Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.Defs

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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.preallocFixed.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (sz : w64),
  d.writable = true → 0 < sz.toInt →
  {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.preallocFixed)) (Val #f))
      (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d }}

end spec

end EtcdGrove
end Perennial
