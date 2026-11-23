/-
`(*bufio.Reader).Read` for the WAL (see `Spec/bufio/Reader__Read.lean`): the generic
`bufio.Reader.Read.specE` at the WAL's stream reader (`Proof/bufio/OwnReaderE.lean`: its
`bufio.ownReader` is a `bufio.ownBufReaderE` at the evidence `E` and buffers of at most 4096
bytes). Until 2026-11-23 a proof of its own; review R1 on #24 (one proof per function).
-/
module

public import Spec.bufio.Reader__Read
public import Spec.bufio.Reader__ReadOk
public import Proof.bufio.OwnReaderE

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

theorem bufio.Reader.Read.wp_proof
    (wp_ReadE : bufio.Reader.Read.specE (GF := GF) (hG := hG)) :
    bufio.Reader.Read.spec (GF := GF) (hG := hG) := by
  intro b ri S E r p xs
  iintro #Hrs #Hbd %Φ !> ⟨%hlen, Hown, Hp⟩ HΦ
  ihave HownE := bufio.ownReader_toE b ri S E r $$ [Hown]
  · iframe Hrs Hbd Hown
  iapply wp_ReadE b ri bufio.walPre S E E (· ≤ 2 ^ 12) r p xs $$ [HownE Hp]
  · iframe HownE Hp
    isplitr
    · ipureintro; intro _; exact hlen
    iintro !> %r' %e H
    iexact H
  iintro !> %n %err ⟨%ys, %Hys, Hp, HownE, #Herr, %hty⟩
  iapply HΦ
  iexists ys
  ihave #Herr' := bufio.walErrAt_of E _ err hty $$ Herr
  ihave Hown := bufio.ownReader_ofE b ri bufio.walPre S E (r ++ ys) $$ HownE
  iframe Hp Hown Herr'
  ipureintro; exact Hys

end proof

end EtcdGrove
end Perennial
