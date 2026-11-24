/-
The proof of `chunkedWriter.Write` (`Net/Spec/net/http/internal/chunkedWriter__Write.lean`): no
chunk for no bytes; otherwise `fmt.Fprintf(cw.Wire, "%x\r\n", len(data))` (its one `Write` of the
length line, `sprintf_hex_crlf`), the sink's `Write` of `data` (all of it, or an error: the short
write's `io.ErrShortWrite` is not reached), `io.WriteString(cw.Wire, "\r\n")` (pending on Perennial:
a hypothesis), and the `Flush` of a `*FlushAfterChunkWriter` sink.
-/
module

public import Net.Spec.net.http.internal.chunkedWriter__Write
public import Perennial.Spec.fmt.Fprintf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http.internal

section pure
variable [GooseExts] [go_gctx : GoGlobalContext] [GoSemanticsFunctions] [go.IntoValInj w64]

/-- `fmt.Sprintf("%x\r\n", n)` of an `int` is `n` in hexadecimal and `"\r\n"`. -/
theorem sprintf_hex_crlf (n : w64) (s : GoString)
    (h : fmt.SprintfOut go!"%x\r\n" [interface.ok (interface.mk go.int #n)] s) :
    s = fmt.hexadecimal (sint.Z n) ++ go!"\r\n" := by
  obtain ⟨o1, rfl, h1⟩ := fmt.SprintfOut.hex_inv (fmt.IntArgValue.int n)
    (fmt.IntArgValue.uniq_int n) h
  obtain ⟨o2, rfl, h2⟩ := fmt.SprintfOut.byte_inv (by decide) h1
  obtain ⟨o3, rfl, h3⟩ := fmt.SprintfOut.byte_inv (by decide) h2
  rw [fmt.SprintfOut.done_inv h3]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.internal.Assumptions]

theorem chunkedWriter.Write.wp_proof
    (wp_Fprintf : fmt.Fprintf.spec (GF := GF) (hG := hG))
    (wp_WriteString : EtcdGrove.io.WriteString.spec (GF := GF) (hG := hG)) :
    chunkedWriter.Write.spec (GF := GF) (hG := hG) := by
  intro cw wi W B out p xs dq
  wp_start as ⟨Hcw, #Hsink, HW, Hp⟩
  iunfold chunkedW at Hcw
  iunfold chunkSink at Hsink
  icases Hsink with ⟨#Hwr, #Hstr, %Hbw, #Hfl⟩
  ihave %Hlen := ownSlice_len $$ Hp
  wp_auto
  wp_if_destruct
  · -- no bytes: no chunk
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen.1]; simp_all)
    subst hx
    iapply HΦ
    iunfold chunkedW
    iframe Hcw Hp
    ileft
    simp only [chunkWire, ↓reduceIte, List.append_nil]
    iframe HW
    ipureintro; simp
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  -- the length line, one `Write` through `fmt.Fprintf`
  wp_apply wp_Fprintf (interface.ok wi) _ _ _ _ (W out) (sinkPost W B out) $$ [$Hsl $HW]
    as %n0 %err0 ⟨-, %s0, %Hs0, Hpost⟩
  · isplitr
    · iapply fmt.argsOk_of_argsWf
      exact fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int _) fmt.ArgsWf.nil
    iexists wi
    isplitr
    · ipureintro; rfl
    unfold fmt.writeSpec
    iintro %sl' %bs %Ψ HW Hsl' HΨ
    iapply Hwr $$ %out %sl' %bs %(DFrac.own 1) [HW Hsl']
    · iframe HW Hsl'
    inext
    iintro %n %err ⟨Hsl', Hq⟩
    iapply HΨ $$ Hsl' Hq
  have hs0 := sprintf_hex_crlf _ _ Hs0
  subst hs0
  iunfold sinkPost at Hpost
  icases Hpost with (⟨⟨%He0, -⟩, HW⟩ | ⟨%He0, HB⟩)
  rotate_left
  · obtain ⟨i0, rfl⟩ : ∃ i, err0 = GoInterface.ok i := by
      cases err0 with
      | nil => exact absurd rfl He0
      | ok i => exact ⟨i, rfl⟩
    wp_auto
    iapply HΦ
    iunfold chunkedW
    iframe Hcw Hp
    iright
    iframe HB
    ipureintro; exact He0
  subst He0
  wp_auto
  -- the chunk's bytes
  wp_apply Hwr $$ %(out ++ (fmt.hexadecimal (sint.Z p.len) ++ go!"\r\n")) %p %xs %dq [$HW $Hp]
    as %n1 %err1 ⟨Hp, Hpost⟩
  iunfold sinkPost at Hpost
  icases Hpost with (⟨⟨%He1, %Hn1⟩, HW⟩ | ⟨%He1, HB⟩)
  rotate_left
  · obtain ⟨i1, rfl⟩ : ∃ i, err1 = GoInterface.ok i := by
      cases err1 with
      | nil => exact absurd rfl He1
      | ok i => exact ⟨i, rfl⟩
    wp_auto
    iapply HΦ
    iunfold chunkedW
    iframe Hcw Hp
    iright
    iframe HB
    ipureintro; exact He1
  subst He1
  have hn1 : n1 = p.len := by word
  subst hn1
  wp_auto
  -- the chunk's `"\r\n"`
  wp_apply wp_WriteString wi go!"\r\n"
      (W ((out ++ (fmt.hexadecimal (sint.Z p.len) ++ go!"\r\n")) ++ xs))
      (sinkPost W B ((out ++ (fmt.hexadecimal (sint.Z p.len) ++ go!"\r\n")) ++ xs) go!"\r\n")
      $$ [$HW] as %n2 %err2 Hpost
  · iapply Hstr
  iunfold sinkPost at Hpost
  icases Hpost with (⟨⟨%He2, -⟩, HW⟩ | ⟨%He2, HB⟩)
  rotate_left
  · obtain ⟨i2, rfl⟩ : ∃ i, err2 = GoInterface.ok i := by
      cases err2 with
      | nil => exact absurd rfl He2
      | ok i => exact ⟨i, rfl⟩
    wp_auto
    iapply HΦ
    iunfold chunkedW
    iframe Hcw Hp
    iright
    iframe HB
    ipureintro; exact He2
  subst He2
  have hne : xs ≠ [] := by
    intro h; subst h; apply Hif; simp at Hlen; word
  have hz : sint.Z p.len = (xs.length : Int) := by rw [Hlen.1]; omega
  have hchunk : out ++ chunkWire xs =
      out ++ (fmt.hexadecimal (sint.Z p.len) ++ go!"\r\n") ++ xs ++ go!"\r\n" := by
    simp only [chunkWire, hne, ↓reduceIte, hz, List.append_assoc]
  wp_auto
  -- a `*FlushAfterChunkWriter` sink is flushed
  by_cases hty : wi.ty = FlushAfterChunkWriter.ty.PointerType
  · obtain ⟨bw, hv⟩ := Hbw hty
    have hwi : wi = ⟨FlushAfterChunkWriter.ty.PointerType, #bw⟩ := by
      cases wi with
      | mk t v => simp only at hty hv; subst hty hv; rfl
    simp only [hty, ↓reduceIte, hv, _root_.decide_true]
    wp_auto
    ihave Hf := Hfl $$ %bw %(out ++ (fmt.hexadecimal (sint.Z p.len) ++ go!"\r\n") ++ xs ++
      go!"\r\n") %hwi
    wp_apply Hf $$ [$HW] as %err3 Hpost
    iunfold sinkPost at Hpost
    rw [List.append_nil] at *
    iapply HΦ
    iunfold chunkedW
    iframe Hcw Hp
    icases Hpost with (⟨⟨%He3, -⟩, HW⟩ | ⟨%He3, HB⟩)
    · ileft
      rw [hchunk]
      iframe HW
      ipureintro; exact ⟨He3, by rw [hz]⟩
    · iright
      iframe HB
      ipureintro; exact He3
  · simp only [hty, ↓reduceIte, _root_.decide_false]
    wp_auto
    iapply HΦ
    iunfold chunkedW
    iframe Hcw Hp
    ileft
    rw [hchunk]
    iframe HW
    ipureintro; exact ⟨rfl, by rw [hz]⟩

end proof

end net.http.internal
end Perennial
