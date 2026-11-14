/-
`fileutil.preallocExtend(f, sizeInBytes)` on a file whose resources are **split between the caller
and atomic updates** (I3b of `notes/wal-fsext-plan.md`; `preallocExtend.lean` for the whole-resource
spec and the premises): the caller's half of the `OsMeta`, its tie `K`, the supplies of the growth's
updates (`fallocSup`, `syscall.Fallocate.wp_growAuW`) and of the fallback's truncate's
(`os.truncSup`). Post: the offset unchanged, the file grown to some `w` between its size and
`sizeInBytes`, all of it on success, at half (`preGrownH`), and `K`. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/preallocExtendAu.lean`. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.DefsAu
public import LinuxFs.Proof.os.Off

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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtend.specAu : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta) (o sz : w64)
    (K : IProp GF),
  0 ≤ fd.toInt → d.writable = true → m.maps = ∅ → 0 ≤ o.toInt → o.toInt ≤ 0xffffffff000 →
  0 < sz.toInt → sz.toInt ≤ 0xffffffff000 → m.size ≤ sz.toNat →
  {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own (1 : Qp).half) m ∗ K ∗
      fallocSup (GF := GF) K d.ino sz.toNat ∗ os.truncSup (GF := GF) K d.ino sz.toNat }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtend)) (Val #f))
      (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ os.ownOff f o ∗ osFd fd dq d ∗ K ∗
      ∃ w : Nat, ⌜m.size ≤ w ∧ w ≤ sz.toNat ∧ (err = interface.nil → w = sz.toNat)⌝ ∗
        preGrownH d.ino m w (err = interface.nil ∧ m.ZeroPg) }}

end spec

end EtcdGrove
end Perennial
