/-
`fileutil.Preallocate(f, sizeInBytes, extendFile)` on a file whose resources are **split between the
caller and atomic updates** (I3b of `notes/wal-fsext-plan.md`; `Preallocate.lean` for the
whole-resource spec and the premises): the caller's half of the `OsMeta`, its tie `K`, the supplies
of `preallocExtend.specAu`'s updates. Post: the offset unchanged; extending, the file grown to some
`w` between its size and `sizeInBytes`, all of it on success, at half (`preGrownH`); not extending,
the file as it was; and `K`. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/PreallocateAu.lean`. Lean-first.
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

/-- What `Preallocate` leaves of the caller's half of the file `i` of `OsMeta` `m`. -/
def preallocPostH (i : Ino) (m : OsMeta) (sz : Nat) (ext : Bool) (err : GoInterface) : IProp GF :=
  if ext then iprop(∃ w : Nat, ⌜m.size ≤ w ∧ w ≤ sz ∧ (err = interface.nil → w = sz)⌝ ∗
    preGrownH i m w)
  else osMeta i (DFrac.own (1 : Qp).half) m

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate.specAu : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta) (o sz : w64)
    (ext : Bool) (K : IProp GF),
  0 ≤ fd.toInt → d.writable = true → m.maps = ∅ → 0 ≤ o.toInt → o.toInt ≤ 0xffffffff000 →
  0 ≤ sz.toInt → sz.toInt ≤ 0xffffffff000 → (ext = true → m.size ≤ sz.toNat) →
  {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own (1 : Qp).half) m ∗ K ∗
      fallocSup (GF := GF) K d.ino sz.toNat ∗ os.truncSup (GF := GF) K d.ino sz.toNat }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate)) (Val #f))
      (Val #sz)) (Val #ext))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ os.ownOff f o ∗ osFd fd dq d ∗ K ∗
      preallocPostH d.ino m sz.toNat ext err }}

end spec

end EtcdGrove
end Perennial
