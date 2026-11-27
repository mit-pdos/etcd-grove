/-
The proof of `Spec/google_golang_org/grpc/appendHeaderBlock.lean`: the first loop sums the block's
length (`hbLenPre`, below `2 ^ 32` by `headerListOk`); the second appends each field's bytes
(`hbBytesPre`).
-/
module

public import Spec.google_golang_org.grpc.appendHeaderBlock
public import Spec.encoding.binary.bigEndian__AppendUint32
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.Assumptions]
variable [binary_sem : encoding.binary.Assumptions]

open github_com.mit_pdos.perennial.goose.model.strings in
theorem grpc.appendHeaderBlock.wp_proof
    (wp_AppendUint32 : binary.bigEndian.AppendUint32.spec (GF := GF) (hG := hG)) :
    grpc.appendHeaderBlock.spec (GF := GF) (hG := hG) := by
  intro b vs kind s hs dq hok
  wp_start as ⟨Hb, Hcap, Hs⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  have hlenP : (hfPairs hs).length = hs.length := by simp [hfPairs]
  have hfull := hbLenPre_le (hfPairs hs) (hfPairs hs).length
  have hcnt := listOk_length _ hok
  have hok' := hok
  unfold headerListOk maxHeaderBlock at hok'
  unfold maxHeaderBlock at hcnt
  wp_auto
  -- the first loop: the block's length
  ihave IH : iprop(∃ (j nv : w64) (fv : google_golang_org.grpc.headerField),
      "i" ∷ i_ptr ↦ j ∗ "n" ∷ n_ptr ↦ nv ∗ "f" ∷ f_ptr ↦ fv ∗
      "Hs" ∷ s ↦*{dq} hs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ hs.length ∧
        sint.Z nv = 4 + hbLenPre (hfPairs hs) (sint.nat j)⌝) $$ [i n f Hs]
  · iexists W64 0, W64 4, _
    simp only [named]
    iframe
    ipureintro
    rw [show sint.nat (W64 0) = 0 by decide]
    simp [hbLenPre]; rfl
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat j < hs.length := by word
    obtain ⟨h, Hh⟩ : ∃ h, hs[sint.nat j]? = some h := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, by word⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index s (sint.Z j) _ dq h Hj.1 $$ [$Hs] as Hs
    · ipureintro; rw [show (sint.Z j).toNat = sint.nat j by rfl]; exact Hh
    wp_apply wp_string_len as %HlN
    wp_apply wp_string_len as %HlV
    obtain ⟨_, hget⟩ := List.getElem?_eq_some_iff.mp Hh
    have hpair : (hfPairs hs)[sint.nat j]'(by omega) = (h.Name', h.Value') := by
      simp [hfPairs, hget]
    have hsucc := hbLenPre_succ (hfPairs hs) (sint.nat j) (by omega)
    rw [hpair] at hsucc
    simp only at hsucc
    have hfld := listOk_field (hfPairs hs) hok (sint.nat j) (by omega)
    rw [hpair] at hfld
    simp only [maxHeaderBlock] at hfld
    have htot := hbLenPre_le (hfPairs hs) (sint.nat j + 1)
    wp_for_post
    iframe
    iexists j + W64 1, _, h
    simp only [named]
    iframe
    ipureintro
    have hn1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    rw [hn1]
    refine ⟨by word, by omega, ?_⟩
    rw [hsucc]
    word
  · -- the loop is done; the header
    have hn : sint.nat j = hs.length := by word
    obtain ⟨-, -, hnv⟩ := Hj
    rw [hn, ← hlenP, hbLen_full] at hnv
    clear Hif hn j fv
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [kind]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append (V := w8) b vs _ [kind] (DFrac.own 1) $$ [$Hb $Hcap $Hsl]
      as %b1 ⟨Hb1, Hcap1, -⟩
    wp_apply wp_AppendUint32 b1 _ _ $$ [$Hpkg $Hb1 $Hcap1] as %b2 ⟨Hb2, Hcap2⟩
    wp_apply wp_AppendUint32 b2 _ _ $$ [$Hpkg $Hb2 $Hcap2] as %b3 ⟨Hb3, Hcap3⟩
    have hpre : vs ++ [kind] ++ (u32Le (W32 (sint.Z nv))).reverse ++
        (u32Le (W32 (sint.Z s.len))).reverse =
        vs ++ kind :: (be32 (4 + ((hfPairs hs).map fun f => 8 + f.1.length + f.2.length).sum) ++
          be32 (hfPairs hs).length) := by
      rw [u32Le_reverse, u32Le_reverse]
      have h1 : uint.nat (W32 (sint.Z nv)) =
          4 + ((hfPairs hs).map fun f => 8 + f.1.length + f.2.length).sum := by
        rw [hbLen_full] at hfull; word
      have h2 : uint.nat (W32 (sint.Z s.len)) = (hfPairs hs).length := by word
      rw [h1, h2]; simp
    -- the second loop: the fields' bytes
    ihave IH : iprop(∃ (j : w64) (bv : GoSlice) (fv : google_golang_org.grpc.headerField),
        "i" ∷ i_ptr ↦ j ∗ "b" ∷ b_ptr ↦ bv ∗ "f" ∷ f_ptr ↦ fv ∗
        "Hb" ∷ bv ↦* (vs ++ kind :: (be32 (4 + ((hfPairs hs).map fun f =>
          8 + f.1.length + f.2.length).sum) ++ be32 (hfPairs hs).length ++
          hbBytesPre (hfPairs hs) (sint.nat j))) ∗
        "Hcap" ∷ ownSliceCap w8 bv (DFrac.own 1) ∗ "Hs" ∷ s ↦*{dq} hs ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ hs.length⌝) $$ [i b f Hb3 Hcap3 Hs]
    · iexists W64 0, b3, _
      simp only [named]
      rw [show sint.nat (W64 0) = 0 by decide]
      simp only [hbBytesPre, List.take_zero, List.map_nil, List.flatten_nil, List.append_nil]
      rw [← hpre]
      iframe
      ipureintro
      refine ⟨by decide, by omega⟩
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat j < hs.length := by word
      obtain ⟨h, Hh⟩ : ∃ h, hs[sint.nat j]? = some h := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, by word⟩
      rw [ite_eq_left Hbnd]
      wp_apply wp_load_slice_index s (sint.Z j) _ dq h Hj.1 $$ [$Hs] as Hs
      · ipureintro; rw [show (sint.Z j).toNat = sint.nat j by rfl]; exact Hh
      wp_apply wp_string_len as %HlN
      wp_apply wp_AppendUint32 bv _ _ $$ [$Hpkg $Hb $Hcap] as %c1 ⟨Hc1, Hccap1⟩
      wp_apply wp_string_to_bytes h.Name' as %n1 ⟨Hn1, -⟩
      wp_apply wp_slice_append (V := w8) c1 _ n1 _ (DFrac.own 1) $$ [$Hc1 $Hccap1 $Hn1]
        as %c2 ⟨Hc2, Hccap2, -⟩
      wp_apply wp_string_len as %HlV
      wp_apply wp_AppendUint32 c2 _ _ $$ [$Hpkg $Hc2 $Hccap2] as %c3 ⟨Hc3, Hccap3⟩
      wp_apply wp_string_to_bytes h.Value' as %n2 ⟨Hn2, -⟩
      wp_apply wp_slice_append (V := w8) c3 _ n2 _ (DFrac.own 1) $$ [$Hc3 $Hccap3 $Hn2]
        as %c4 ⟨Hc4, Hccap4, -⟩
      obtain ⟨_, hget⟩ := List.getElem?_eq_some_iff.mp Hh
      have hlenP' : sint.nat j < (hfPairs hs).length := by omega
      have hpair : (hfPairs hs)[sint.nat j]'hlenP' = (h.Name', h.Value') := by
        simp [hfPairs, hget]
      have hsucc := hbBytesPre_succ (hfPairs hs) (sint.nat j) hlenP'
      rw [hpair] at hsucc
      have hfld := listOk_field (hfPairs hs) hok (sint.nat j) hlenP'
      rw [hpair] at hfld
      simp only [maxHeaderBlock] at hfld
      have hN : uint.nat (W32 (sint.Z (W64 (h.Name'.length : Int)))) = h.Name'.length := by word
      have hV : uint.nat (W32 (sint.Z (W64 (h.Value'.length : Int)))) = h.Value'.length := by word
      rw [u32Le_reverse, u32Le_reverse, hN, hV]
      wp_for_post
      iframe
      iexists j + W64 1, c4, h
      simp only [named]
      have hn1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [hn1, hsucc]
      simp only [fieldBytes, List.append_assoc, List.cons_append]
      iframe
      ipureintro
      refine ⟨by word, by omega⟩
    · -- the loop is done: the whole block
      have hn : sint.nat j = hs.length := by word
      rw [hn, ← hlenP, hbBytes_full]
      iapply HΦ
      simp only [headerBlock, List.append_assoc, List.cons_append]
      iframe

end proof

end EtcdGrove
end Perennial
