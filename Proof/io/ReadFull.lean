/-
`io.ReadFull` of a stream reader, proved over Perennial's translation of Go's `ReadFull`/`ReadAtLeast`
(Perennial's `io.wp_ReadFull`, over its `io.readerOk` contract, which a stream reader meets:
`io.readerStream_readerOk`). Until 2026-11-21 an axiom (WAL leaf specs, 2026-11-13; restated
2026-11-14 with the reader's errors carried with their Iris evidence, `io.readFullRes`).
-/
module

public import Spec.io.ReadFull
public import Perennial.Proof.io.Link

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
variable [package_sem : _root_.Perennial.io.Assumptions]

theorem io.ReadFull.wp_proof : io.ReadFull.spec (GF := GF) (hG := hG) := by
  intro ri S E r0 p xs eof ueof
  iintro #Hr
  ihave #Hok := io.readerStream_readerOk ri S E $$ Hr
  imodintro
  iintro %Φ ⟨#Hpkg, #Heof, #Hueof, %Hlen, HS, Hp⟩ HΦ
  wp_apply _root_.Perennial.io.wp_ReadFull ri (fun r m => r.length + m < 2 ^ 62) S E r0 p xs eof
      ueof $$ [HS Hp] as %n %err ⟨%ys, %Hys, Hp, HS, #Hres⟩
  · iframe Hok Heof Hueof HS Hp
    ipureintro
    intro ys hys
    simp only [List.length_append]
    omega
  iapply HΦ
  iexists ys
  iframe Hp HS
  isplitl []
  · ipureintro; exact Hys
  unfold io.readFullRes
  unfold _root_.Perennial.io.readFullRes at *
  iexact Hres

end proof

end EtcdGrove
end Perennial
