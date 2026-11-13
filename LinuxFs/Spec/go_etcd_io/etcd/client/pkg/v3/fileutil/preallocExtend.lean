/-
`fileutil.preallocExtend(f, sizeInBytes)` (preallocate_unix.go): `syscall.Fallocate(fd, 0, 0,
sizeInBytes)`, a growth of the file to `sizeInBytes`; on `ENOTSUP` or `EINTR` (`errors.As` into an
`Errno`) the fallback `preallocExtendTrunc`.

The premises are `preallocExtendTrunc`'s (the file at most `sizeInBytes` long, unmapped, the offset
known), `sizeInBytes` positive (`Preallocate` skips 0), and `errors`' package initialized (for
`errors.As`). Post: the offset unchanged, the file grown to some `w` between its size and
`sizeInBytes`, all of it on success (`preGrown`: the new bytes a zero run). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/preallocExtend.lean`. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.Defs
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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtend.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta) (o sz : w64),
  0 ≤ fd.toInt → d.writable = true → m.maps = ∅ → 0 ≤ o.toInt → o.toInt ≤ 0xffffffff000 →
  0 < sz.toInt → sz.toInt ≤ 0xffffffff000 → m.size ≤ sz.toNat →
  {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own 1) m }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtend)) (Val #f))
      (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ os.ownOff f o ∗ osFd fd dq d ∗
      ∃ w : Nat, ⌜m.size ≤ w ∧ w ≤ sz.toNat ∧ (err = interface.nil → w = sz.toNat)⌝ ∗
        preGrown d.ino m w }}

end spec

end EtcdGrove
end Perennial
