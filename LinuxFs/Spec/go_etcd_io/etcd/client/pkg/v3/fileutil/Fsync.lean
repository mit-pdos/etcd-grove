/-
`fileutil.Fsync(f)` (sync_linux.go): `f.Sync()`, so its spec is `os.File.Sync.spec`'s: with the
whole of the file's `OsMeta` and the bytes it may not have made durable (`m.Covers`), whole. On
success the size and every byte are durable (`OsMeta.synced`, `durB`); on failure nothing changes.
Proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/Fsync.lean`. Lean-first (WAL, plan
W2's "not done" list).
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Spec.os.File__Sync

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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta) (lo : Nat)
    (xs : List ByteG),
  m.Covers lo xs.length →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
      osBytes (GF := GF) d.ino lo (DFrac.own 1) xs }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync)) (Val #f))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ osMeta d.ino (DFrac.own 1) m.synced ∗
          osBytes d.ino lo (DFrac.own 1) (xs.map (fun x => durB x.1))) ∨
       (⌜err ≠ interface.nil⌝ ∗ osMeta d.ino (DFrac.own 1) m ∗
          osBytes d.ino lo (DFrac.own 1) xs)) }}

end spec

end EtcdGrove
end Perennial
