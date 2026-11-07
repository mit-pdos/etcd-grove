/-
`os.File.ReadAt.specRacy` (`Spec/os/File__ReadAt.lean`) with the `io.EOF` case as Fs v1 stated it:
the bytes read reach every held byte inside `[off, off + len(b))`. The Fs v2 port of the shared spec
dropped that clause (its docstring still states it), and minibolt's `Snapshot` needs it: it panics
when an `io.EOF` read is shorter than its transaction. The semantics gives it (a `pread` returns up
to a size `fstat` could see, which is past every held byte: `statSees_gt`), so this is a local copy,
proved in `Proof/.../bboltfs/ReadAtRacy.lean` from a local copy of `wp_osPRead_racy_list` that also
says so; to be dropped once the shared spec states it again. Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- `f.ReadAt(b, off)` racing writers (see the file header): `os.File.ReadAt.specRacy`, and with
`io.EOF` every held byte of the range is below `off + n`. -/
abbrev ReadAtRacy.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (vs : List w8)
    (off : w64) (dq : DFrac) (d : OsFd) (rs : List (Nat × DFrac × List (w8 × Bool)))
    (eof : GoInterface),
  d.readable = true → 0 ≤ off.toInt → vs.length ≤ 0x40000000 → off.toNat + vs.length < 2 ^ 63 →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦* vs ∗
      osFd (GF := GF) fd dq d ∗
      ([∗list] r ∈ rs, osBytes (GF := GF) d.ino r.1 r.2.1 r.2.2) ∗
      globalAddr io.EOF ↦□ eof }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"ReadAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ([∗list] r ∈ rs, osBytes d.ino r.1 r.2.1 r.2.2) ∗
      ∃ vs' : List w8, sl ↦* vs' ∗
        ⌜vs'.length = vs.length ∧ n.toNat ≤ vs.length ∧
          (∀ i b, os.heldByte rs i b → off.toNat ≤ i → i < off.toNat + n.toNat →
            vs'[i - off.toNat]? = some b) ∧
          ((err = interface.nil ∧ n.toNat = vs.length) ∨
           (err = eof ∧ ∀ i b, os.heldByte rs i b → off.toNat ≤ i →
              i < off.toNat + vs.length → i < off.toNat + n.toNat) ∨
           (∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe))⌝ }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
