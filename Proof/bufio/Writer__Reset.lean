/-
`(*bufio.Writer).Reset` (see `Spec/bufio/Writer__Reset.lean`).
-/
module

public import Spec.bufio.Writer__Reset

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

theorem bufio.Writer.Reset.wp_proof : bufio.Writer.Reset.spec (GF := GF) (hG := hG) := by
  intro bw sz w
  wp_start as ⟨%Hw, Hraw⟩
  iunfold bufio.rawWriter at Hraw
  icases Hraw with ⟨%v, %bs, Hb, Hbuf, %Hv⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  have hnn : v.buf' ≠ slice.nil := by
    intro h; rw [h] at Hlen
    have h0 : sint.nat (slice.nil : GoSlice).len = 0 := by decide
    rw [h0] at Hlen
    omega
  rcases Hw with rfl | ⟨wi, rfl, hty⟩
  all_goals wp_auto
  all_goals try simp only [Ne.symm hty, ↓reduceIte]
  all_goals try wp_auto
  all_goals try simp only [hnn, decide_false]
  all_goals try wp_auto
  all_goals
    iapply HΦ
    iunfold bufio.rawWriter
    iexists _, bs
    iframe Hb Hbuf
    ipureintro; exact ⟨Hv.1, Hv.2.1, rfl⟩

end proof

end EtcdGrove
end Perennial
