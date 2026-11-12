/-
`Open`'s reads of the file's meta pages (U11, `notes/bbolt-proof-plan.md`): `os.File.ReadAt` of
bytes the reader holds whole (`osBytes p.ino 0 dq xs`), without the file's `OsMeta`, from the racing
read's spec, strengthened (`os.File.ReadAt.specRacyLt`, `Spec/os/File__ReadAt.lean`, batch 36).

**Why not `os.File.ReadAt.spec`/`specRacy` as they are** (reported to the maintainer): both allow an
in-bounds read to fail with `io.EOF` (`spec`: `(0, err)` with any `err ≠ nil`; `specRacy`: `eof`
with `n = len(b)`). `getPageSize` treats `io.EOF` as a short file and probes further: past page 1
(position `8192`) it may read user data that happens to hold a valid meta with another page size,
which `Open` would adopt (D18's bug, through the spec's slack). The model (`TrustedCode/os.lean`)
returns `io.EOF` only when a `pread` reads nothing with `len(b) > 0`, so `n < len(b)`; and its
`*PathError` is `fmtErrorOk` (`Proof/os/ErrorOk.lean`).
-/
module

public import Spec.os.File__ReadAt
public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [osA : os.Assumptions]

omit osA in
/-- **A read of held bytes**: `f.ReadAt(b, off)` inside bytes `xs` of the file held from offset
`0` (no `OsMeta`): all of them, exactly (`n = len(b)`), or a `*PathError` (`fmt` formats it). -/
theorem os.File.ReadAt.wp_held (hRead : os.File.ReadAt.specRacyLt (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (vs : List w8)
    (off : w64) (dq dqb : DFrac) (d : OsFd) (xs : List ByteG) (eof : GoInterface)
    (hrd : d.readable = true) (hoff : 0 ≤ off.toInt) (hn : vs.length ≤ 0x40000000)
    (hin : off.toNat + vs.length ≤ xs.length) (hx : xs.length < 2 ^ 63) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦* vs ∗
        osFd (GF := GF) fd dq d ∗ osBytes (GF := GF) d.path 0 dqb xs ∗
        globalAddr io.EOF ↦□ eof }}
      (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"ReadAt")) (Val #sl))
        (Val #off))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        os.ownFile f fd name dqf ∗ osFd fd dq d ∗ osBytes d.path 0 dqb xs ∗
        ∃ vs' : List w8, sl ↦* vs' ∗
          ⌜(err = interface.nil ∧ n = W64 (vs.length : Int) ∧
              vs' = ((xs.map Prod.fst).drop off.toNat).take vs.length) ∨
            (∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)⌝ ∗
        fmtErrorOkOrNil err }} := by
  iintro %Φ ⟨#Hinv, Hfo, Hsl, Hfd, Hb, #Heof⟩ HΦ
  iapply hRead f fd name dqf sl vs off dq d [(0, dqb, xs)] eof hrd hoff hn (by omega)
    $$ [Hfo Hsl Hfd Hb]
  · iframe; iframe #
    iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro %n %err ⟨Hfo, Hfd, Hb, %vs', Hsl, %h, Hr⟩
  icases BigSepL.bigSepL_singleton.1 $$ Hb with Hb
  obtain ⟨hl, hnl, hex⟩ := h
  have held : ∀ i, i < xs.length → ∀ b, (xs[i]?).map Prod.fst = some b →
      os.heldByte [(0, dqb, xs)] i b := fun i _ b hb =>
    ⟨_, List.Mem.head _, Nat.zero_le _, by simpa using hb⟩
  icases Hr with (%hc | ⟨%pe, %hpe, #Hek⟩)
  · rcases hc with ⟨rfl, hfull⟩ | ⟨rfl, hlt, hall⟩
    · iapply HΦ
      iframe Hfo Hfd Hb
      iexists vs'
      iframe Hsl
      isplitr
      · ipureintro
        left
        refine ⟨rfl, by apply BitVec.eq_of_toNat_eq; simp; omega, ?_⟩
        apply List.ext_getElem?
        intro j
        by_cases hj : j < vs.length
        · have hi : off.toNat + j < xs.length := by omega
          obtain ⟨b, hb⟩ : ∃ b, (xs[off.toNat + j]?).map Prod.fst = some b :=
            ⟨(xs[off.toNat + j]).1, by simp [List.getElem?_eq_getElem hi]⟩
          have := hex (off.toNat + j) b (held _ hi b hb) (by omega) (by omega)
          rw [show off.toNat + j - off.toNat = j by omega] at this
          rw [this]
          simp only [List.getElem?_take, hj, ite_true, List.getElem?_drop, List.getElem?_map]
          simpa using hb.symm
        · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
      simp only [fmtErrorOkOrNil]; itrivial
    · exfalso
      have hi : off.toNat + n.toNat < xs.length := by omega
      have := hall (off.toNat + n.toNat) (xs[off.toNat + n.toNat]).1
        (held _ hi _ (by simp [List.getElem?_eq_getElem hi])) (by omega) (by omega)
      omega
  · subst hpe
    iapply HΦ
    iframe Hfo Hfd Hb
    iexists vs'
    iframe Hsl
    isplitr
    · ipureintro; right; exact ⟨pe, rfl⟩
    simp only [fmtErrorOkOrNil, interface.mkOk]
    iexact Hek

end spec

end EtcdGrove
end Perennial
