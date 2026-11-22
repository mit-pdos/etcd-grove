/-
The proof of `writeFrame` (`Net/Spec/.../lib/remote/writeFrame.lean`): `b := make([]byte,
8+len(body))` (no overflow: `len(body) ≤ maxLen`), `putU64` of the length into `b[:8]`,
`copy(b[8:], body)` (`wp_slice_copy`, on `b` split at 8), so that `b` holds `frame body`, then
`writeAll` of `b`.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.putU64
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.writeAll
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.writeFrame

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- A body of at most `maxLen` bytes has its length below `2 ^ 20`. -/
theorem len_le_maxLen (body : GoSlice) (bd : List w8) (Hmax : bd.length ≤ maxLen)
    (Hlen : bd.length = sint.nat body.len ∧ 0 ≤ sint.Z body.len) : sint.Z body.len ≤ 2 ^ 20 := by
  have e : sint.nat body.len = (sint.Z body.len).toNat := rfl
  have h1 := Hlen.1
  have h2 : bd.length ≤ 2 ^ 20 := Hmax
  omega

theorem writeFrame.wp_proof (wp_putU64 : putU64.spec (GF := GF) (hG := hG))
    (wp_writeAll : writeAll.spec (GF := GF) (hG := hG)) :
    writeFrame.spec (GF := GF) (hG := hG) := by
  intro c cn s a P W0 body bd dq ed Hmax
  wp_start as ⟨#Hc, Hbody, #Hed, Htok, #HP⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbody
  wp_auto
  have hZ := len_le_maxLen body bd Hmax Hlen
  have hbl : uint.nat body.len = bd.length := by word
  have h8 : sint.nat (W64 8 + body.len) = 8 + bd.length := by word
  wp_apply (wp_slice_make2 (V := w8) (W64 8 + body.len)) as %b ⟨Hb, -⟩
  · ipureintro; word
  rw [h8]
  wp_apply wp_putU64 b _ body.len (by simp) $$ Hb as Hb
  rw [List.drop_replicate, show 8 + bd.length - 8 = bd.length by omega]
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  ihave %Hbw := ownSlice_wf _ _ _ $$ Hb
  have hbL : sint.Z b.len = 8 + bd.length := by
    have e : sint.nat b.len = (sint.Z b.len).toNat := rfl
    simp only [List.length_append, u64Le_length, List.length_replicate] at Hbl
    omega
  have h8' : sint.Z (W64 8) = 8 := rfl
  rw [ite_eq_left ⟨by decide, by omega, Hbw.2⟩]
  icases (ownSlice_split_all (W64 8) b _ _ ⟨by decide, by omega⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
  have hs8 : sint.nat (W64 8) = 8 := rfl
  rw [hs8, List.take_left' (u64Le_length _), List.drop_left' (u64Le_length _)]
  wp_auto
  wp_apply wp_slice_copy (slice.slice b w8 (W64 8) b.len) _ body bd dq $$ [Hb2 Hbody]
    as %n ⟨-, Hb2, Hbody⟩
  · iframe
  rw [List.length_replicate, List.take_length, List.drop_replicate, Nat.sub_self,
    List.replicate_zero, List.append_nil]
  ihave Hb := ownSlice_combine (W64 8) b _ _ bd (W64 0) b.len ⟨by simp [u64Le_length]; rfl,
    by decide, by decide, by omega⟩ $$ Hb1 Hb2
  ihave Hb := (ownSlice_trivial_slice b _ _).2 $$ Hb
  have hfr : u64Le body.len ++ bd = frame bd := by
    rw [frame]; congr 2; word
  rw [hfr]
  wp_auto
  wp_apply wp_writeAll c cn s a P W0 b (frame bd) (DFrac.own 1) ed $$ [Hb Htok]
    as %ok ⟨%w, -, Htok, %Hw⟩
  · iframe Hb Htok Hc Hed HP
  iapply HΦ
  iexists w
  iframe Hbody Htok
  ipureintro; exact Hw

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
