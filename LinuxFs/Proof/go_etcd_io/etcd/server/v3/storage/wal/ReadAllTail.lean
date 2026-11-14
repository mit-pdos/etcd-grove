/- Lean-first (no Rocq counterpart).

# `ReadAll` after its loop: the decoder's files lent out (W3/W5 of `notes/wal-fsext-plan.md`, twenty-second session)

At `io.EOF` the decoder has read everything; what `ReadAll` still asks of it (S/wal.go:622-670) is
`LastOffset()` (before the tail's `Seek`) and `LastCRC()` (for `newFileEncoder`, after `ZeroToEnd`
changed the tail). `ownDecoder_lend` gives every file's stream state out of the decoder (`F.S q`, for
the WAL's segments `walFileS`: the file, its offset, the program's halves) and keeps the residue
`decResid` (the CRC digest), over which `LastCRC` answers the decoder's CRC
(`decoder.LastCRC.wp_resid`, the proof of `decoder__LastCRC.lean` on the residue).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastCRC
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Sum32

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- **What is left of a decoder whose files are lent out** (see the file header): its CRC digest at `c`. -/
def decResid (d : Loc) (c : w32) : IProp GF :=
  iprop(∃ h : GoInterface,
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"crc" d ↦ h ∗ ownDecCrc h c)

/-- The files' readers give their streams' states out. -/
theorem ownFbrs_lend (IoE : GoInterface → Prop) (eof : GoInterface) :
    ∀ (fbrs : List Loc) (fs : List (DecFile GF)) (rs : List (List w8)),
    ownFbrs IoE eof fbrs fs rs ⊢ [∗list] F ∈ fs, ∃ q, F.S q
  | [], [], [] => by
    iintro -; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | fbr :: fbrs, F :: fs, r :: rs => by
    simp only [ownFbrs]
    iintro ⟨Hf, Hs⟩
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitl [Hf]
    · iunfold ownFbr at Hf
      icases Hf with ⟨%b, %fi, %err, -, -, Hb, -⟩
      icases bufio.ownReader_open b F.fr _ _ r $$ Hb with ⟨%q, HS, -⟩
      iexists r ++ q
      iexact HS
    · iapply ownFbrs_lend IoE eof fbrs fs rs $$ Hs
  | [], _ :: _, _ => by simp only [ownFbrs]; iintro %h; cases h
  | [], [], _ :: _ => by simp only [ownFbrs]; iintro %h; cases h
  | _ :: _, [], _ => by simp only [ownFbrs]; iintro %h; cases h
  | _ :: _, _ :: _, [] => by simp only [ownFbrs]; iintro %h; cases h

/-- **The decoder's files lent out** (see the file header). -/
theorem ownDecoder_lend (d : Loc) (IoE : GoInterface → Prop) (eof : GoInterface)
    (fs : List (DecFile GF)) (off : Nat) (c : w32) (live : Bool) :
    ownDecoder d IoE eof fs off c live ⊢ ([∗list] F ∈ fs, ∃ q, F.S q) ∗ decResid d c := by
  unfold ownDecoder decResid
  iintro ⟨%sl, %fbrs, %h, %rs, -, -, -, -, Hcrc, -, Hdc, Hf, -⟩
  isplitl [Hf]
  · iapply ownFbrs_lend IoE eof fbrs fs rs $$ Hf
  · iexists h
    iframe

/-- The streams of the files a decoder left, gathered: those left before (`fs.take kD`, the decoder then over
`fs.drop kD`) and those its last call left (`decPostB`'s `fsD.take k`). -/
theorem leftS_merge (fs fsD : List (DecFile GF)) (kD k : Nat) (h : fsD = fs.drop kD) :
    ([∗list] F ∈ fs.take kD, ∃ q, F.S q) ∗ ([∗list] F ∈ fsD.take k, ∃ q, F.S q) ⊢
      [∗list] F ∈ fs.take (kD + k), ∃ q, F.S q := by
  subst h
  rw [List.take_add]
  exact (BigSepL.bigSepL_append (Φ := fun _ (F : DecFile GF) => iprop(∃ q, F.S q))).2

/-- **`d.LastCRC()` on the residue** (`decoder__LastCRC.lean`'s proof). -/
theorem go_etcd_io.etcd.server.v3.storage.wal.decoder.LastCRC.wp_resid
    (HSum : go_etcd_io.etcd.pkg.v3.crc.digest.Sum32.spec (GF := GF) (hG := hG)) (d : Loc) (c : w32) :
    {{ decResid (hG := hG) d c }}
      (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.decoder.ty @!! go!"LastCRC")) (Val #()))
    {{ RET #c; decResid d c }} := by
  wp_start as Hd
  iunfold decResid at Hd
  icases Hd with ⟨%h, Hcrc, Hdc⟩
  iunfold ownDecCrc at Hdc
  icases Hdc with ⟨%l, %tab, %Hh, Hl, #Htab⟩
  subst Hh
  wp_auto
  wp_apply HSum $$ [Hl] as Hl
  · iexact Hl
  iapply HΦ
  iunfold decResid
  iexists _
  iframe
  iunfold ownDecCrc
  iexists l, tab
  iframe
  iframe Htab
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
