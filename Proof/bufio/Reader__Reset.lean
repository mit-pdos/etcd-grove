/-
`(*bufio.Reader).Reset` (see `Spec/bufio/Reader__Reset.lean`).
-/
module

public import Spec.bufio.Reader__Reset

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

/-- `b.reset(buf, rd)`: the reader's struct replaced by a fresh one over `buf` and `rd`. -/
theorem bufio.wp_reset_rr (b : Loc) (v : _root_.Perennial.bufio.Reader) (buf : GoSlice)
    (rd : GoInterface) :
    {{ (b ↦ v : IProp GF) }}
      (App (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"reset"))
        (Val #buf)) (Val #rd))
    {{ RET #(); ∃ v' : _root_.Perennial.bufio.Reader, b ↦ v' ∗
        ⌜v'.buf' = buf ∧ v'.rd' = rd ∧ v'.r' = W64 0 ∧ v'.w' = W64 0 ∧
          v'.err' = interface.nil⌝ }} := by
  wp_start as Hv
  wp_auto
  iapply HΦ
  iexists _
  iframe Hv
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bufio.Reader.Reset.wp_proof : bufio.Reader.Reset.spec (GF := GF) (hG := hG) := by
  intro b rd
  wp_start as ⟨%Hrd, Hraw⟩
  iunfold bufio.rawReader at Hraw
  icases Hraw with ⟨%v, %bs, Hb, Hbuf, %Hv⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  have hnn : v.buf' ≠ slice.nil := by
    intro h; rw [h] at Hlen
    have h0 : sint.nat (slice.nil : GoSlice).len = 0 := by decide
    rw [h0] at Hlen
    omega
  rcases Hrd with rfl | ⟨ri, rfl, hty⟩
  all_goals wp_auto
  all_goals try simp only [Ne.symm hty, ↓reduceIte]
  all_goals try wp_auto
  all_goals try simp only [hnn, decide_false]
  all_goals try wp_auto
  all_goals
    wp_apply bufio.wp_reset_rr $$ [$Hb] as ⟨%v', Hb, %Hv'⟩
    iapply HΦ
    iunfold bufio.freshReader
    iexists v', bs
    obtain ⟨hb, hr, hr0, hw0, he⟩ := Hv'
    rw [hb]
    iframe Hb Hbuf
    ipureintro
    exact ⟨hr, hr0, hw0, he, Hv.1, Hv.2⟩

end proof

end EtcdGrove
end Perennial
