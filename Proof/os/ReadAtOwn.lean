/-
The racing read of bytes the reader holds (S4, 2026-11-18): `os.File.ReadAt.specRacyLt`
(`Spec/os/File__ReadAt.lean`) at `P := [∗list] osBytes rs`, with the trivial accessor
(`os.heldAcc_own`), so that a client holding its bytes states nothing of the accessor. Its
hypothesis is the callee spec; it imports no proof. Lean-first.
-/
module

public import Spec.os.File__ReadAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The racing read of held bytes**: `specRacyLt` with the ranges `rs` held across the call (the
form `specRacyLt` had before S4). -/
theorem os.File.ReadAt.wp_racyLtOwn (hRead : os.File.ReadAt.specRacyLt (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (vs : List w8)
    (off : w64) (dq : DFrac) (d : OsFd) (rs : List (Nat × DFrac × List ByteG))
    (eof : GoInterface)
    (hrd : d.readable = true) (hoff : 0 ≤ off.toInt) (hn2 : vs.length ≤ 0x40000000)
    (hend : off.toNat + vs.length < 2 ^ 63) :
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
            vs'[i - off.toNat]? = some b)⌝ ∗
        (⌜(err = interface.nil ∧ n.toNat = vs.length) ∨
           (err = eof ∧ n.toNat < vs.length ∧ ∀ i b, os.heldByte rs i b → off.toNat ≤ i →
              i < off.toNat + vs.length → i < off.toNat + n.toNat)⌝ ∨
         (∃ pe : Loc, ⌜err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe⌝ ∗
           fmtErrorOk err ∗ ⌜¬ FsNoErr⌝)) }} := by
  iintro %Φ ⟨#Hinv, Hfo, Hsl, Hfd, Hbs, #Heof⟩ HΦ
  ihave #Hacc := os.heldAcc_own (GF := GF) d.ino rs
  iapply hRead f fd name dqf sl vs off dq d rs
    ([∗list] r ∈ rs, osBytes (GF := GF) d.ino r.1 r.2.1 r.2.2) ⊤ eof hrd hoff hn2 hend
    CoPset.subseteq_top $$ [Hfo Hsl Hfd Hbs]
  · iframe; iframe #
  inext
  iintro %n %err ⟨Hfo, Hfd, Hbs, Hr⟩
  iapply HΦ
  iframe

end spec

end EtcdGrove
end Perennial
