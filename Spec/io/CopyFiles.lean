/-
`io.Copy(dst, src)` of two files (`wal.Repair`'s `io.Copy(bf, f)`, S/repair.go:73: `bf` the new `*os.File`
`<segment>.broken`, `f` the segment's `*fileutil.LockedFile`). **A hypothesis** of `wal.Repair.wp_proof`, not
an axiom, until its proof (`io.Copy`/`copyBuffer` have bodies at the Perennial pin; the proof's state:
`notes/wal-units/tester.md`, the last handoff). The Go path (Go 1.27.3,
linux/amd64; `notes/wal-fsext-plan.md`, "io.Copy log"): `copyBuffer` → the source's promoted `File.WriteTo`
→ `genericWriteTo` → the destination's `File.ReadFrom` → `copy_file_range` rounds (the part's trusted
`model.copyFileRangeRound`: a `PRead` at the source's offset then a `PWrite` of what it read at the
destination's, both offsets moved by the count), or, from an empty rest or an unhandled errno,
`genericReadFrom`'s 32 KiB `File.Read`/`File.Write` loop.

The statement (the io.Copy log's, for an empty destination, what `Repair` copies into): the destination
`dst` an `*os.File` open for writing at offset 0 on a file `i` held whole and empty (`trFile i True`, what the
`O_TRUNC` open gives); the source `src` a `*fileutil.LockedFile` embedding the `*os.File` `f`, open for
reading at the offset `o` on a file at rest whose page cache is the bytes `bs` (any fractions of its
`OsMeta` and bytes: the copy only reads it). Afterwards both files are open as before, the source's state
unchanged, the destination held whole again (`io.copyDst`: `trFile i False`'s shape) and its offset and the
source's somewhere; on success (`err = nil`) the destination's bytes are the source's from `o` on and both
offsets at the ends. The count `n` claims nothing (`nonissues/go-os-readfrom-count-after-fallback.md`), and
on an error nothing is claimed of the offsets nor of the destination's bytes (a short write moves the
source's offset past the destination's: the io.Copy log's "both offsets moved by `k`" holds only on
success). The source is below `2^61` bytes: a `copy_file_range` round of up to `0x7ffff000` bytes past
`2^62` is not modelled (`model.copyFileRangeRound`, a panic; ledger 2026-11-22). Lean-first.
-/
module

public import Spec.os.OpenFileTruncS
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The destination after the copy** (see the file header): the file `i` whole, as `trFile i False`,
its bytes' values `P`. -/
def io.copyDst (i : Ino) (P : List w8 → Prop) : IProp GF :=
  iprop(∃ (m : OsMeta) (xs : List ByteG), osMeta i (DFrac.own 1) m ∗
    osBytes i 0 (DFrac.own 1) xs ∗ mcellsAny (GF := GF) m.maps 0 m.size ∗
    ⌜xs.length = m.size ∧ m.maps = ∅ ∧ m.cut = none ∧ m.lo ≤ m.size ∧ m.ZfGe ∧ P (xs.map (·.1))⌝)

theorem io.copyDst_trFile (i : Ino) (P : List w8 → Prop) :
    io.copyDst (GF := GF) i P ⊢ trFile i False := by
  unfold io.copyDst trFile
  iintro ⟨%m, %xs, Hm, Hb, Hc, %h⟩
  iexists m, xs
  iframe
  ipureintro
  exact ⟨h.1, False.elim, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, False.elim⟩

/-- See the file header. -/
abbrev io.CopyFiles.spec : Prop :=
  ∀ (bf : Loc) (fdd : w64) (nd : GoString) (dd : OsFd) (lf f : Loc) (fds : w64) (ns : GoString)
    (ds : OsFd) (o : w64) (qm qb : DFrac) (m : OsMeta) (bs : List ByteG),
  dd.writable = true → ds.readable = true → 0 ≤ fdd.toInt → 0 ≤ fds.toInt → 0 ≤ o.toInt →
  o.toNat ≤ bs.length → bs.length = m.size → m.size < 2 ^ 61 →
  {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.os ∗
      os.ownFile bf fdd nd (DFrac.own 1) ∗ osFd fdd (DFrac.own 1) dd ∗ os.ownOff bf (W64 0) ∗
      trFile dd.ino True ∗
      fileutil.lockedFile lf f ∗ os.ownFile f fds ns (DFrac.own 1) ∗ osFd fds (DFrac.own 1) ds ∗
      os.ownOff f o ∗ osMeta ds.ino qm m ∗ osBytes ds.ino 0 qb bs }}
    (App (App (Val (@! _root_.Perennial.io.Copy))
      (Val #(interface.mkOk (go.GoType.PointerType os.File.ty) #bf)))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) #lf)))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile bf fdd nd (DFrac.own 1) ∗ osFd fdd (DFrac.own 1) dd ∗
      os.ownFile f fds ns (DFrac.own 1) ∗ osFd fds (DFrac.own 1) ds ∗
      osMeta ds.ino qm m ∗ osBytes ds.ino 0 qb bs ∗
      io.copyDst dd.ino (fun vs => err = interface.nil → vs = (bs.map (·.1)).drop o.toNat) ∗
      ∃ (od os' : w64), os.ownOff bf od ∗ os.ownOff f os' ∗
        ⌜err = interface.nil → os' = W64 bs.length ∧ od = W64 (bs.length - o.toNat)⌝ }}

end spec

end EtcdGrove
end Perennial
