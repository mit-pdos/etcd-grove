/-
(hraft_robust R3) The proof of `disk.(*reader).bytes`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.reader__uint64
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.reader__bytes

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.disk

theorem rb_sint (n : Nat) (h : n < 2 ^ 63) : sint.Z (W64 (n : Int)) = n := by word

theorem rb_uint (n : Nat) (h : n < 2 ^ 63) : uint.Z (W64 (n : Int)) = n := by word

theorem rb_nlt (n : Nat) (len : w64) (m : Nat) (h : n < 2 ^ 63) (hm : n ≤ m)
    (hl : m = sint.nat len ∧ 0 ≤ sint.Z len) : ¬ uint.Z len < uint.Z (W64 (n : Int)) := by
  obtain ⟨h1, h2⟩ := hl; word

theorem rb_le (n : Nat) (len : w64) (m : Nat) (h : n < 2 ^ 63) (hm : n ≤ m)
    (hl : m = sint.nat len ∧ 0 ≤ sint.Z len) : sint.Z (W64 (n : Int)) ≤ sint.Z len := by
  obtain ⟨h1, h2⟩ := hl; word

theorem rb_nat (n : Nat) (h : n < 2 ^ 63) : sint.nat (W64 (n : Int)) = n := by
  show (sint.Z (W64 (n : Int))).toNat = n
  rw [rb_sint n h]; simp

theorem github_com.hashicorp.raft.examples.hraftnet.disk.reader.bytes.wp_proof
    (wp_uint64 : github_com.hashicorp.raft.examples.hraftnet.disk.reader.uint64.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.reader.bytes.spec (GF := GF) (hG := hG) := by
  intro r cs rest hcs
  wp_start as Hr
  wp_auto
  rw [show encBytes cs ++ rest = encU64 (W64 cs.length) ++ (cs ++ rest) by simp [encBytes]]
  wp_apply wp_uint64 $$ [$Hr] as Hr
  iunfold readerSt at Hr
  icases Hr with ⟨%sl, Hr, #Hsl⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hwf := ownSlice_wf $$ Hsl
  have hm : cs.length ≤ (cs ++ rest).length := by simp
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (cs.length : Int)) ∧
      sint.Z (W64 (cs.length : Int)) ≤ sint.Z sl.len :=
    ⟨by decide, by rw [rb_sint _ hcs]; exact Int.natCast_nonneg _, rb_le _ _ _ hcs hm Hlen⟩
  wp_auto
  wp_if_destruct
  · exfalso; exact rb_nlt _ _ _ hcs hm Hlen Hif
  wp_apply wp_slice_make2 (V := w8) (W64 (cs.length : Int)) as %out ⟨Hout, Hcap⟩
  · ipureintro; rw [rb_sint _ hcs]; exact Int.natCast_nonneg _
  ihave Hparts := (ownSlice_slice (W64 0) (W64 (cs.length : Int)) sl DFrac.discard (cs ++ rest) hb).1 $$ Hsl
  icases Hparts with ⟨-, #Hmid, #Hsuf⟩
  have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 (cs.length : Int))) (cs ++ rest) = cs := by
    rw [rb_nat _ hcs, show sint.nat (W64 0) = 0 from rfl]; simp [subslice]
  have hdrop : (cs ++ rest).drop (sint.nat (W64 (cs.length : Int))) = rest := by
    rw [rb_nat _ hcs]; simp
  have hc1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (cs.length : Int)) ∧
      sint.Z (W64 (cs.length : Int)) ≤ sint.Z sl.cap := ⟨hb.1, hb.2.1, Int.le_trans hb.2.2 Hwf.2⟩
  have hc2 : 0 ≤ sint.Z (W64 (cs.length : Int)) ∧ sint.Z (W64 (cs.length : Int)) ≤ sint.Z sl.len ∧
      sint.Z sl.len ≤ sint.Z sl.cap := ⟨by rw [rb_sint _ hcs]; exact Int.natCast_nonneg _, hb.2.2, Hwf.2⟩
  simp only [hc1, _root_.and_self, ↓reduceIte]
  wp_apply wp_slice_copy (V := w8) out _ (slice.slice sl w8 (W64 0) (W64 (cs.length : Int))) _ DFrac.discard
    $$ [$Hout $Hmid] as %m ⟨%Hm, Hout, -⟩
  simp only [hc2, _root_.and_self, ↓reduceIte]
  wp_auto
  iapply HΦ
  isplitl [Hr]
  · iunfold readerSt
    iexists _
    iframe Hr
    iapply (show (slice.slice sl w8 (W64 (cs.length : Int)) sl.len ↦*□
        (cs ++ rest).drop (sint.nat (W64 (cs.length : Int))) : IProp GF) ⊢
      slice.slice sl w8 (W64 (cs.length : Int)) sl.len ↦*□ rest by rw [hdrop]) $$ Hsuf
  iframe Hcap
  have hfin : ∀ X : List w8, X = cs → (out ↦* X : IProp GF) ⊢ out ↦* cs := by
    intro X h; rw [h]
  iapply (hfin _ (by rw [rb_nat _ hcs]; simp [subslice])) $$ Hout

end proof

end Perennial
