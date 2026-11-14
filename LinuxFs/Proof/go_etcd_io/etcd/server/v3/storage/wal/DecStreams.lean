/-
**The decoder's file streams out of it** (W10's `Close` of a handle not yet read, `WAL.Close.specOpening`;
the W7-W12 log, fifth session): a decoder (`ownDecoder`) holds each file's stream state `F.S` inside its
`*bufio.Reader` (`bufio.ownReader`, at the bytes delivered and buffered). `Close` does not read the
decoder: it closes the files and syncs the tail through `w.locks`, and puts the program's halves of the
segments back into `walInv`'s parked state, all of which sit in the streams (`walFileS`, `ReadDefs.lean`:
the file, its fd, the halves of the segment's `OsMeta` and bytes). `ownDecoder_streams` gives every
stream's state, at some position, discarding the decoder. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- Each file's stream state, out of its reader (see the file header). -/
theorem ownFbrs_streams (IoE : GoInterface → Prop) (eof : GoInterface) :
    ∀ (fbrs : List Loc) (fs : List (DecFile GF)) (rs : List (List w8)),
    ownFbrs IoE eof fbrs fs rs ⊢ [∗list] F ∈ fs, ∃ r, F.S r
  | [], [], [] => by
    iintro -
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | fbr :: fbrs, F :: fs, r :: rs => by
    simp only [ownFbrs]
    iintro ⟨Hf, Hs⟩
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitl [Hf]
    · iunfold ownFbr at Hf
      icases Hf with ⟨%b, %fi, %err, -, -, Hb, -, -⟩
      icases bufio.ownReader_open b F.fr F.S _ r $$ Hb with ⟨%q, HS, -⟩
      iexists r ++ q; iexact HS
    · iapply ownFbrs_streams IoE eof fbrs fs rs $$ Hs
  | [], _ :: _, _ => by simp only [ownFbrs]; iintro %h; cases h
  | [], [], _ :: _ => by simp only [ownFbrs]; iintro %h; cases h
  | _ :: _, [], _ => by simp only [ownFbrs]; iintro %h; cases h
  | _ :: _, _ :: _, [] => by simp only [ownFbrs]; iintro %h; cases h

/-- **Every file's stream state, out of the decoder** (see the file header). -/
theorem ownDecoder_streams (d : Loc) (IoE : GoInterface → Prop) (eof : GoInterface)
    (fs : List (DecFile GF)) (off : Nat) (c : w32) (live : Bool) :
    ownDecoder d IoE eof fs off c live ⊢ [∗list] F ∈ fs, ∃ r, F.S r := by
  unfold ownDecoder
  iintro ⟨%sl, %fbrs, %h, %rs, -, -, -, -, -, -, -, Hf, -⟩
  iapply ownFbrs_streams IoE eof fbrs fs rs $$ Hf

end lemmas

end WalFs
end EtcdGrove
end Perennial

end
