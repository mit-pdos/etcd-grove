/-
`(*bufio.Writer).Available` (see `Spec/bufio/Writer__Available.lean`).
-/
module

public import Spec.bufio.Writer__Available
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

theorem bufio.Writer.Available.wp_proof : bufio.Writer.Available.spec (GF := GF) (hG := hG) := by
  intro bw wi J Q Ew sz sent pend err
  wp_start as Hown
  iunfold bufio.ownBufWriter at Hown
  icases Hown with ⟨#Hpkg, #Hwr, HJ, #HQ, Hrep⟩
  iunfold bufio.writerRep at Hrep
  icases Hrep with ⟨%buf, %n, %rest, Hb, Hbuf, %Hn, #Herr⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  have hl : ((pend ++ rest).length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  obtain ⟨hn, hpos, hsz⟩ := Hn
  simp only [List.length_append] at hl hpos hsz
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; word
  iunfold bufio.ownBufWriter, bufio.writerRep
  iframe Hpkg Hwr HJ HQ
  iexists buf, n, rest
  iframe Hb Hbuf Herr
  ipureintro
  simp only [List.length_append]
  exact ⟨hn, hpos, hsz⟩

end proof

end EtcdGrove
end Perennial
