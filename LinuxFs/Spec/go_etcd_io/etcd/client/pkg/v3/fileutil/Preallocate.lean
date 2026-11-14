/-
`fileutil.Preallocate(f, sizeInBytes, extendFile)` (preallocate.go): nothing for 0; else
`preallocExtend` (grow the file to `sizeInBytes`: the WAL's calls, `filePipeline.alloc`,
`wal.Create`, `ZeroToEnd`) or `preallocFixed` (`FALLOC_FL_KEEP_SIZE`, no visible change).

Premises: `preallocExtend`'s (the file unmapped, the offset known, sizes at most ext4's maximum, and
when extending the file at most `sizeInBytes` long, `nonissues/etcd-fileutil-prealloc-fallback-
shrinks.md`), `errors`' package initialized. Post: the offset unchanged; extending, the file grown to
some `w` between its size and `sizeInBytes`, all of it on success (`preGrown`: the new bytes a zero
run, I4's `osZerosA`; on success the zeros known from the page cache on, `OsMeta.ZeroPg`, if they
were); not extending, the file as it was. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/Preallocate.lean`. Lean-first.
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

/-- What `Preallocate` leaves of the file `i` of `OsMeta` `m`. -/
def preallocPost (i : Ino) (m : OsMeta) (sz : Nat) (ext : Bool) (err : GoInterface) : IProp GF :=
  if ext then iprop(∃ w : Nat, ⌜m.size ≤ w ∧ w ≤ sz ∧ (err = interface.nil → w = sz)⌝ ∗
    preGrown i m w (err = interface.nil ∧ m.ZeroPg))
  else osMeta i (DFrac.own 1) m

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta) (o sz : w64)
    (ext : Bool),
  0 ≤ fd.toInt → d.writable = true → m.maps = ∅ → 0 ≤ o.toInt → o.toInt ≤ 0xffffffff000 →
  0 ≤ sz.toInt → sz.toInt ≤ 0xffffffff000 → (ext = true → m.size ≤ sz.toNat) →
  {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own 1) m }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate)) (Val #f))
      (Val #sz)) (Val #ext))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ os.ownOff f o ∗ osFd fd dq d ∗
      preallocPost d.ino m sz.toNat ext err }}

end spec

end EtcdGrove
end Perennial
