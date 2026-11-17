/-
A racing `f.ReadAt(b, off)` on an open `*os.File` with no I/O error (`File.ReadAt.specRacyLt` over a
semantics whose steps satisfy **no I/O error on chosen files**, `FsStepSat (NoIoErr Sio)`; every
inode covered): no `*PathError`. The result is `nil` with all of `b` read, or `io.EOF` with fewer
bytes than asked, every held byte inside `[off, off + len(b))` among them (the model's `io.EOF`: a
`pread` that read nothing, past the end of the file). bbolt's `Open` reads its meta pages so
(`Proof/go_etcd_io/bbolt/Open/ReadHeld.lean`). Proved in `Proof/os/File__ReadAtNoErr.lean`.
Lean-first.
-/
module

public import Spec.os.File__ReadAt
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

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
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.File.ReadAt.specRacyLtNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (vs : List w8)
    (off : w64) (dq : DFrac) (d : OsFd) (rs : List (Nat × DFrac × List ByteG))
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
           (err = eof ∧ n.toNat < vs.length ∧ ∀ i b, os.heldByte rs i b → off.toNat ≤ i →
              i < off.toNat + vs.length → i < off.toNat + n.toNat))⌝ }}

end spec

end EtcdGrove
end Perennial
