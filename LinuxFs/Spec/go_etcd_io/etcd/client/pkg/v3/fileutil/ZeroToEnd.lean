/-
`fileutil.ZeroToEnd(f)` (fileutil.go): zeros the file from its offset `o` to its end (the WAL's
`ReadAll`, after seeking to the decoder's last offset, wal.go:580-585): `Seek(0, SeekCurrent)`,
`Seek(0, SeekEnd)` (the size `S`), `Truncate(o)`, `Preallocate(f, S, true)` (grow back over
zeros), `Seek(o, SeekStart)`.

Premises: the file unmapped (`Truncate`'s cells, `Preallocate`'s), the offset at most the size
(the WAL's: the decoder's last offset is inside the file), the size at most ext4's maximum;
`errors`' package initialized (`Preallocate`). Pre: the whole `OsMeta` and the bytes from `o` to
the end, whole (`Truncate` cuts them off).

Post on success: the offset `o`, the file of its old size with the same mappings, the bytes from
`o` to the end a zero run of unknown candidates (`osZerosA`: a truncate then a growth before a
sync, every zero with candidates of its own). On an error (the size's `fstat`, the truncate, the
growth): some offset, the file of some size `w ≥ o`, its bytes from `o` some list of `w - o` bytes
(the old bytes, or zeros up to where the growth stopped); no more is promised (the WAL returns the
error and drops the file). Proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/
ZeroToEnd.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate

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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta) (o : w64)
    (xs : List ByteG),
  0 ≤ fd.toInt → d.writable = true → m.maps = ∅ → 0 ≤ o.toInt → o.toNat ≤ m.size →
  m.size ≤ 0xffffffff000 → xs.length = m.size - o.toNat →
  {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
      osBytes (GF := GF) d.ino o.toNat (DFrac.own 1) xs }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd)) (Val #f))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ os.ownOff f o ∗
          ∃ m' : OsMeta, ⌜m'.size = m.size ∧ m'.maps = m.maps⌝ ∗ osMeta d.ino (DFrac.own 1) m' ∗
            osZerosA d.ino o.toNat (m.size - o.toNat) (DFrac.own 1)) ∨
       (⌜err ≠ interface.nil⌝ ∗ ∃ (o' : w64) (m' : OsMeta) (ys : List ByteG),
          ⌜o.toNat ≤ m'.size ∧ m'.maps = m.maps ∧ ys.length = m'.size - o.toNat⌝ ∗
          os.ownOff f o' ∗ osMeta d.ino (DFrac.own 1) m' ∗
          osBytes d.ino o.toNat (DFrac.own 1) ys)) }}

end spec

end EtcdGrove
end Perennial
