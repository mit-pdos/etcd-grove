/-
`bufio.NewReader` for the WAL (see `Spec/bufio/NewReader.lean`): `NewReaderSize(rd, 4096)` by the
generic `bufio.NewReaderSize.specE`, at the WAL's stream reader (`Proof/bufio/OwnReaderE.lean`).
Until 2026-11-23 a proof of its own; review R1 on #24 (one proof per function).
-/
module

public import Spec.bufio.NewReader
public import Spec.bufio.NewReaderSize
public import Proof.bufio.OwnReaderE
public import Proof.bufio.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

theorem bufio.NewReader.wp_proof
    (wp_NewReaderSize : bufio.NewReaderSize.specE (GF := GF) (hG := hG)) :
    bufio.NewReader.spec (GF := GF) (hG := hG) := by
  intro ri S E r hty
  wp_start as ⟨#Hrs, #Hbd, HS⟩
  ihave #Hrd := io.readerStream_readerOk ri S E $$ Hrs
  try wp_auto
  wp_apply wp_NewReaderSize ri bufio.walPre S E E (· ≤ 2 ^ 12) r (W64 4096) $$ [$Hpkg $HS]
    as %br Hbr
  · have h4 : (max (sint.Z (W64 4096)) 16).toNat = 4096 := rfl
    rw [h4]
    isplitr
    · ipureintro; exact hty
    isplitr
    · ipureintro; decide
    isplitr
    · unfold bufio.walPre; iexact Hrd
    unfold bufio.preUpTo bufio.walPre
    iintro !> %r' HS'
    ihave %h := Hbd $$ HS'
    ipureintro
    intro m _ hm
    omega
  try wp_auto
  iapply HΦ
  iapply bufio.ownReader_ofE $$ Hbr

end proof

end EtcdGrove
end Perennial
