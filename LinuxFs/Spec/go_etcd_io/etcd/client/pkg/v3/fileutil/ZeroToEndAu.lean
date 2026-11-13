/-
`fileutil.ZeroToEnd(f)` on a file whose resources are **split between the caller and atomic
updates** (I3b of `notes/wal-fsext-plan.md`; `ZeroToEnd.lean` for the whole-resource spec and the
premises), as `ReadAll`'s on the WAL's tail: the caller's halves of the `OsMeta` and of the bytes
from the offset `o` to the end, its tie `K`, and the supplies of the updates of the truncate to `o`
and of the growth back to the size (`fallocate`, or the fallback's truncate): `os.truncSup` at `o` and
at the size, `fallocSup` at the size.

Post on success: the offset `o`; the caller's half of the `OsMeta`, of the old size and mappings, the
page cache known zero past the size to the end of its last page (`pageEnd m.size ≤ m'.cz`: a sync then
makes the zeros known from the size on, `OsMeta.synced_zf_size`; `os.zeroToEnd_cz` for the metas the
resizes leave); its half of the bytes from `o` to the end, a zero run (`osZerosA`). On an error: some
offset, its half of the `OsMeta` of some size `w ≥ o` and of `w - o` bytes from `o`. Both with `K`.
The update's owner holds the other halves (it committed each step's outcome). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/ZeroToEndAu.lean`. Lean-first.
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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd.specAu : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta) (o : w64)
    (xs : List ByteG) (K : IProp GF),
  0 ≤ fd.toInt → d.writable = true → m.maps = ∅ → 0 ≤ o.toInt → o.toNat ≤ m.size →
  m.size ≤ 0xffffffff000 → xs.length = m.size - o.toNat →
  {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own (1 : Qp).half) m ∗
      osBytes (GF := GF) d.ino o.toNat (DFrac.own (1 : Qp).half) xs ∗ K ∗
      os.truncSup (GF := GF) K d.ino o.toNat ∗ os.truncSup (GF := GF) K d.ino m.size ∗
      fallocSup (GF := GF) K d.ino m.size }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd)) (Val #f))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗ K ∗
      ((⌜err = interface.nil⌝ ∗ os.ownOff f o ∗
          ∃ m' : OsMeta, ⌜m'.size = m.size ∧ m'.maps = m.maps ∧ pageEnd m.size ≤ m'.cz⌝ ∗
            osMeta d.ino (DFrac.own (1 : Qp).half) m' ∗
            osZerosA d.ino o.toNat (m.size - o.toNat) (DFrac.own (1 : Qp).half)) ∨
       (⌜err ≠ interface.nil⌝ ∗ ∃ (o' : w64) (m' : OsMeta) (ys : List ByteG),
          ⌜o.toNat ≤ m'.size ∧ m'.maps = m.maps ∧ ys.length = m'.size - o.toNat⌝ ∗
          os.ownOff f o' ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m' ∗
          osBytes d.ino o.toNat (DFrac.own (1 : Qp).half) ys)) }}

end spec

end EtcdGrove
end Perennial
