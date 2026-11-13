/-
`fileutil.Fdatasync(f)` (sync_linux.go): `syscall.Fdatasync(int(f.Fd()))`, so its spec is
`syscall.Fdatasync.spec`'s, the error `errnoErr e`: with the whole of the file's `OsMeta` and the
bytes it may not have made durable (`m.Covers`), whole. On success the size and every byte are
durable; on failure (never `EINTR`) nothing changes. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/Fdatasync.lean`. Lean-first.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Spec.syscall.Fdatasync
public import LinuxFs.Spec.os.File__Fd

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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta) (lo : Nat)
    (xs : List ByteG),
  m.Covers lo xs.length →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
      osBytes (GF := GF) d.ino lo (DFrac.own 1) xs }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync)) (Val #f))
  {{ (e : w64), RET #(errnoErr e); os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜e = 0⌝ ∗ osMeta d.ino (DFrac.own 1) m.synced ∗
          osBytes d.ino lo (DFrac.own 1) (xs.map (fun x => durB x.1))) ∨
       (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗ osMeta d.ino (DFrac.own 1) m ∗
          osBytes d.ino lo (DFrac.own 1) xs)) }}

end spec

end EtcdGrove
end Perennial
