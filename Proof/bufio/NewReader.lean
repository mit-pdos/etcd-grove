/-
`bufio.NewReader` for the WAL (see `Spec/bufio/NewReader.lean`): the generic `bufio.NewReader.specE`
at the WAL's stream reader (`Proof/bufio/OwnReaderE.lean`). Until 2026-11-23 a proof of its own;
review R1 on #24 (one proof per function); an instance of `NewReader.specE` since round 2 (N4).
-/
module

public import Spec.bufio.NewReader
public import Spec.bufio.NewReaderOk
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
    (wp_NewReaderE : bufio.NewReader.specE (GF := GF) (hG := hG)) :
    bufio.NewReader.spec (GF := GF) (hG := hG) := by
  intro ri S E r hty
  iintro %Φ ⟨#Hpkg, #Hrs, #Hbd, HS⟩ HΦ
  ihave #Hrd := io.readerStream_readerOk ri S E $$ Hrs
  iapply wp_NewReaderE ri bufio.walPre S E E (· ≤ 2 ^ 12) r $$ [HS]
  · iframe Hpkg HS
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
  iintro !> %br Hbr
  iapply HΦ
  iapply bufio.ownReader_ofE $$ Hbr

end proof

end EtcdGrove
end Perennial
