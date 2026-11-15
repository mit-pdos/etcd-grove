/- Lean-first (no Rocq counterpart). The proof of `encodeOracle` (W4c U5). -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.encodeOracle
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putOps
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putHS
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putU64
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putOps

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section pure
variable [GooseExts]

/-- A candidate's bytes in `encodeOracle`. -/
def tCandBytes (c : TCand) : List w8 := tOpsBytes c.h ++ tU64 c.unl ++ tU64 c.pur

end pure

theorem list_set_self {α : Type} (l : List α) (n : Nat) (x : α) (h : l[n]? = some x) :
    l.set n x = l := by
  obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact List.set_getElem_self hn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem encodeOracle.wp_proof (wp_putU64 : putU64.spec (GF := GF) (hG := hG))
    (wp_putHS : putHS.spec (GF := GF) (hG := hG))
    (wp_putOps : putOps.spec (GF := GF) (hG := hG)) :
    encodeOracle.spec (GF := GF) (hG := hG) := by
  intro v o
  wp_start as Hr
  iunfold oracleRep at Hr
  icases Hr with ⟨%Hf, Hcs, #Hsince, Hscap, #Hop, Hopcap⟩
  obtain ⟨hcr, hsy, hlh⟩ := Hf
  iunfold candsOwn at Hcs
  icases Hcs with ⟨%cvs, Hcs, Hcscap, #Hce⟩
  iunfold candsElems at Hce
  icases Hce with ⟨%Hcel, #Hcall⟩
  ihave %Hcslen := ownSlice_len $$ Hcs
  ihave %Hoplen := ownSlice_len $$ Hop
  wp_auto
  wp_apply +noauto (wp_slice_make2 (V := w8) (W64 0)) as %b0 ⟨Hb, Hcap⟩
  · ipureintro; word
  simp only [List.replicate_zero]
  wp_auto
  wp_join iprop(∃ bb1 : GoSlice, b_ptr ↦ bb1 ∗
      bb1 ↦* tU64 (if o.created then W64 1 else W64 0) ∗ ownSliceCap w8 bb1 (DFrac.own 1))
    at next with [b Hb Hcap] as ⟨%bb1, b, Hb, Hcap⟩
  · rw [← hcr]
    cases v.created'
    · wp_auto
      wp_apply wp_putU64 $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
      wp_join_done
      iexists b2
      iframe
    · wp_auto
      wp_apply wp_putU64 $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
      wp_join_done
      iexists b2
      iframe
  wp_apply wp_putU64 $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
  ihave HI : (∃ (c : w64) (bb : GoSlice),
      "c" ∷ c_ptr ↦ c ∗ "b" ∷ b_ptr ↦ bb ∗ "o" ∷ o_ptr ↦ v ∗ "Hcs" ∷ v.cands' ↦* cvs ∗
      "Hb" ∷ bb ↦* (tU64 (if o.created = true then W64 1 else W64 0) ++ tU64 v.cands'.len ++
        (o.cands.take (sint.nat c)).flatMap tCandBytes) ∗
      "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
      "%Hc" ∷ ⌜0 ≤ sint.Z c ∧ sint.Z c ≤ sint.Z v.cands'.len⌝ : IProp GF) $$ [c b o Hcs Hb Hcap]
  · iexists W64 0, b2
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil,
      List.append_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have hcl : sint.nat c < cvs.length := by
      have : sint.nat c < sint.nat v.cands'.len := by word
      omega
    obtain ⟨cv, Hcv⟩ : ∃ cv, cvs[sint.nat c]? = some cv := ⟨_, List.getElem?_eq_getElem hcl⟩
    obtain ⟨cd, Hcd⟩ : ∃ cd, o.cands[sint.nat c]? = some cd :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hcel]; exact hcl)⟩
    ihave #Hcr : candRep cv cd $$ []
    · iapply Hcall; ipureintro; exact ⟨Hcv, Hcd⟩
    iunfold candRep at Hcr
    icases Hcr with ⟨%Hcf, #Hch⟩
    have hb : 0 ≤ sint.Z c ∧ sint.Z c < sint.Z v.cands'.len := ⟨Hc.1, Hif⟩
    icases ownSlice_elem_acc (sint.Z c) cv v.cands' (DFrac.own 1) cvs Hc.1
      (by simpa [sint.nat] using Hcv) $$ Hcs with ⟨Hv, Hclose⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_auto
    wp_apply wp_putOps $$ [$Hb $Hcap $Hch] as %b3 ⟨Hb, Hcap⟩
    repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
    wp_apply wp_putU64 $$ [$Hb $Hcap] as %b4 ⟨Hb, Hcap⟩
    repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
    wp_apply wp_putU64 $$ [$Hb $Hcap] as %b5 ⟨Hb, Hcap⟩
    ihave Hcs := Hclose $$ Hv
    rw [list_set_self cvs _ cv (by simpa [sint.nat] using Hcv)]
    wp_for_post
    iframe
    iexists c + W64 1, b5
    have hc1 : sint.nat (c + W64 1) = sint.nat c + 1 := by word
    rw [hc1, flatMap_take_succ o.cands tCandBytes _ cd Hcd]
    unfold tCandBytes
    rw [← Hcf.1, ← Hcf.2]
    simp only [List.append_assoc]
    iframe
    ipureintro; constructor <;> word
  · have hcn : sint.nat c = o.cands.length := by
      have : sint.nat c = sint.nat v.cands'.len := by word
      omega
    rw [flatMap_take_length o.cands tCandBytes _ hcn]
    wp_apply wp_putOps $$ [$Hb $Hcap $Hsince] as %b3 ⟨Hb, Hcap⟩
    wp_apply wp_putU64 $$ [$Hb $Hcap] as %b4 ⟨Hb, Hcap⟩
    wp_apply wp_putHS $$ [$Hb $Hcap] as %b5 ⟨Hb, Hcap⟩
    wp_apply wp_putU64 $$ [$Hb $Hcap] as %b6 ⟨Hb, Hcap⟩
    ihave HI2 : (∃ (i : w64) (bb : GoSlice),
        "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗ "o" ∷ o_ptr ↦ v ∗
        "Hb" ∷ bb ↦* (tU64 (if o.created = true then W64 1 else W64 0) ++ tU64 v.cands'.len ++
          List.flatMap tCandBytes o.cands ++ tOpsBytes o.since ++ tU64 v.synced' ++
          tHsBytes v.lastHS' ++ tU64 v.opens'.len ++ (o.opens.take (sint.nat i)).flatMap tU64) ∗
        "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v.opens'.len⌝ : IProp GF) $$ [i b o Hb Hcap]
    · iexists W64 0, b6
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil,
        List.append_nil]
      iframe
      ipureintro; constructor <;> word
    wp_for HI2
    wp_if_destruct
    · have hil : sint.nat i < o.opens.length := by
        have : sint.nat i < sint.nat v.opens'.len := by word
        omega
      obtain ⟨x, Hx⟩ : ∃ x, o.opens[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
      have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z v.opens'.len := ⟨Hi.1, Hif⟩
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index v.opens' (sint.Z i) o.opens DFrac.discard x Hi.1 $$ [Hop] as -
      · isplitl []
        · iexact Hop
        · ipureintro; exact Hx
      wp_apply wp_putU64 $$ [$Hb $Hcap] as %c1 ⟨Hb, Hcap⟩
      wp_for_post
      iframe
      iexists i + W64 1, c1
      have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hi1, flatMap_take_succ o.opens tU64 _ x Hx]
      simp only [List.append_assoc]
      iframe
      ipureintro; constructor <;> word
    · have hin : sint.nat i = o.opens.length := by
        have : sint.nat i = sint.nat v.opens'.len := by word
        omega
      rw [flatMap_take_length o.opens tU64 _ hin]
      wp_apply wp_bytes_to_string $$ Hb as -
      have henc : tU64 (if o.created = true then W64 1 else W64 0) ++ tU64 v.cands'.len ++
          List.flatMap tCandBytes o.cands ++ tOpsBytes o.since ++ tU64 v.synced' ++
          tHsBytes v.lastHS' ++ tU64 v.opens'.len ++ List.flatMap tU64 o.opens =
          tEncodeOracle o := by
        unfold tEncodeOracle tCandBytes
        rw [hsy, hlh, ← w64_of_length o.cands v.cands'.len (Hcel ▸ Hcslen),
          ← w64_of_length o.opens v.opens'.len Hoplen]
      rw [henc]
      iapply HΦ
      iunfold oracleRep
      isplitr
      · ipureintro; exact ⟨hcr, hsy, hlh⟩
      iframe
      isplitl
      · iunfold candsOwn; iexists cvs; iframe
        iunfold candsElems
        isplitr
        · ipureintro; exact Hcel
        iexact Hcall
      isplitl []
      · iexact Hsince
      · iexact Hop

end proof

end etcd_wal
end EtcdGrove
end Perennial
