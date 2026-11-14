/- Lean-first (no Rocq counterpart). The proof of `fromRaft`. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.fromRaft
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.entData
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Getters
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.entData

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal go_etcd_io.raft.v3 WalEnc WalFs

section pure
variable [GooseExts]

theorem tEntData_length' (e : TEnt) : (tEntData e).length = uint.nat e.size' := by
  rw [tEntData_eq]; simp; omega

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem fromRaft.wp_proof (wp_entData : entData.spec (GF := GF) (hG := hG)) :
    fromRaft.spec (GF := GF) (hG := hG) := by
  intro re m
  wp_start as #Hin
  simp only [walRaftP]
  iunfold walEntIn at Hin
  icases Hin with ⟨#Hc, %Hsm⟩
  wp_auto
  wp_apply (wp_entRoC_GetData re (walEntCanon m)) $$ [] as %ds #Hds
  · iexact Hc
  have hD : (if m.Data' = [] then none else some m.Data').getD [] = m.Data' := by
    split <;> simp_all
  rw [hD]
  ihave %Hdl := ownSlice_len $$ Hds
  ihave HI : (∃ (i : w64),
      "i" ∷ i_ptr ↦ i ∗
      "salt" ∷ salt_ptr ↦ (List.range (sint.nat i)).foldl (tSaltStep m.Data') (W64 0) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ min 8 m.Data'.length⌝ : IProp GF) $$ [i salt]
  · iexists W64 0
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · by_cases hlt : sint.Z i < sint.Z ds.len
    · rw [if_pos (by simp [hlt])]
      have hil : sint.nat i < m.Data'.length := by
        have : sint.nat i < sint.nat ds.len := by word
        omega
      obtain ⟨b, Hb⟩ : ∃ b, m.Data'[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem hil⟩
      have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ds.len := ⟨Hi.1, hlt⟩
      icases ownSlice_elem_acc (sint.Z i) b ds DFrac.discard m.Data' Hi.1
        (by simpa [sint.nat] using Hb) $$ Hds with ⟨Hbv, -⟩
      wp_auto
      iterate 3 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      wp_for_post
      iframe
      iexists i + W64 1
      have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hi1, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have hst : ∀ x, tSaltStep m.Data' x (sint.nat i) = x ||| W64 (uint.Z b) <<< (W64 8 * i) := by
        intro x
        unfold tSaltStep
        rw [Hb, Option.getD_some, show (W64 ((sint.nat i : Nat) : Int)) = i by word]
      rw [hst]
      iframe
      ipureintro
      constructor <;> word
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hin : sint.nat i = min 8 m.Data'.length := by
        have : sint.nat i = sint.nat ds.len := by word
        omega
      rw [hin]
      try wp_auto
      wp_apply (wp_entRoC_GetIndex re (walEntCanon m)) $$ []
      · iexact Hc
      wp_apply (wp_entRoC_GetTerm re (walEntCanon m)) $$ []
      · iexact Hc
      have hdsl : ds.len = W64 (m.Data'.length : Int) := by word
      have hE : (⟨m.Index', m.Term', ds.len,
        List.foldl (tSaltStep m.Data') (W64 0) (List.range (min 8 m.Data'.length))⟩ : TEnt) =
          tFromRaftE m := by
        rw [hdsl]; rfl
      rw [hE]
      have hEs : uint.nat (tFromRaftE m).size' = m.Data'.length := by
        simp only [tFromRaftE]; word
      wp_apply (wp_entData (tFromRaftE m) (by rw [hEs]; have := Hdl.1; word)) as %wt ⟨Hwt, -⟩
      imod ownSlice_persist $$ Hwt with #Hwt
      ihave %Hwl := ownSlice_len $$ Hwt
      have hwl : (tEntData (tFromRaftE m)).length = m.Data'.length := by rw [tEntData_length', hEs]
      ihave HI2 : (∃ (i : w64),
          "i" ∷ i_ptr ↦ i ∗
          "e" ∷ e_ptr ↦ (if m.Data'.take (sint.nat i) = (tEntData (tFromRaftE m)).take (sint.nat i) then
            tFromRaftE m else { tFromRaftE m with size' := W64 0 }) ∗
          "%Hi2" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z ds.len⌝ : IProp GF) $$ [i e]
      · iexists W64 0
        rw [show sint.nat (W64 0) = 0 from rfl]
        simp only [List.take_zero, ite_true]
        iframe
        ipureintro; constructor <;> word
      wp_for HI2
      by_cases hlt2 : sint.Z i < sint.Z ds.len
      · first
        | rw [if_pos (show decide (sint.Z i < sint.Z ds.len) = true by simp [hlt2])]
        | rw [if_pos (show decide ((#(decide (sint.Z i < sint.Z ds.len)) : val) = #true) = true by simp [hlt2])]
        have hil2 : sint.nat i < m.Data'.length := by
          have : sint.nat i < sint.nat ds.len := by word
          omega
        obtain ⟨x, Hx⟩ : ∃ x, m.Data'[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hil2⟩
        obtain ⟨y, Hy⟩ : ∃ y, (tEntData (tFromRaftE m))[sint.nat i]? = some y :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ds.len := ⟨Hi2.1, hlt2⟩
        have hb3 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z wt.len := ⟨Hi2.1, by word⟩
        icases ownSlice_elem_acc (sint.Z i) x ds DFrac.discard m.Data' Hi2.1
          (by simpa [sint.nat] using Hx) $$ Hds with ⟨Hxv, -⟩
        icases ownSlice_elem_acc (sint.Z i) y wt DFrac.discard _ Hi2.1
          (by simpa [sint.nat] using Hy) $$ Hwt with ⟨Hyv, -⟩
        wp_auto
        iterate 4 (try simp only [hb2, hb3, _root_.and_self, ↓reduceIte]; try wp_auto)
        have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        have hstep := take_succ_eq_iff Hx Hy
        wp_if_destruct
        · wp_for_post
          iframe
          iexists i + W64 1
          rw [hi1]
          have hxy : x = y := by simpa using Hif
          have hiff : (List.take (sint.nat i + 1) m.Data' = List.take (sint.nat i + 1) (tEntData (tFromRaftE m))) ↔
              (List.take (sint.nat i) m.Data' = List.take (sint.nat i) (tEntData (tFromRaftE m))) := by
            rw [hstep]; simp [hxy]
          simp only [hiff]
          iframe
          ipureintro; constructor <;> word
        · wp_for_post
          iframe
          iexists i + W64 1
          have hn : ¬ (List.take (sint.nat i + 1) m.Data' = List.take (sint.nat i + 1) (tEntData (tFromRaftE m))) := by
            rw [hstep]; intro h; exact Hif (by simpa using h.2)
          rw [hi1, if_neg hn]
          have hcur : ∀ v : TEnt, v = tFromRaftE m ∨ v = { tFromRaftE m with size' := W64 0 } →
              { v with size' := W64 0 } = { tFromRaftE m with size' := W64 0 } := by
            rintro v (rfl | rfl) <;> rfl
          rw [hcur (if List.take (sint.nat i) m.Data' = List.take (sint.nat i) (tEntData (tFromRaftE m)) then
              tFromRaftE m else { tFromRaftE m with size' := W64 0 })
            (by by_cases h : List.take (sint.nat i) m.Data' = List.take (sint.nat i) (tEntData (tFromRaftE m)) <;>
              simp [h])]
          iframe
          ipureintro; constructor <;> word
      · simp only [hlt2, decide_false, Bool.false_eq_true, ↓reduceIte, val_false_ne_true, _root_.decide_true,
    not_false_eq_true]
        have hin2 : sint.nat i = m.Data'.length := by
          have : sint.nat i = sint.nat ds.len := by word
          omega
        rw [hin2, List.take_length, show (tEntData (tFromRaftE m)).take m.Data'.length =
          tEntData (tFromRaftE m) by rw [← hwl, List.take_length]]
        wp_auto
        by_cases hdq : m.Data' = tEntData (tFromRaftE m)
        · have h1 : tFromRaft m = tFromRaftE m := by unfold tFromRaft; simp [hdq]
          rw [h1, if_pos hdq]; iapply HΦ; itrivial
        · have h1 : tFromRaft m = ⟨m.Index', m.Term', W64 0, tSaltOf m.Data'⟩ := by
            unfold tFromRaft; rw [if_neg hdq]; rfl
          rw [h1, if_neg hdq]; iapply HΦ; itrivial

  · have hin : sint.nat i = min 8 m.Data'.length := by
      have : 8 ≤ sint.nat i := by word
      omega
    rw [hin]
    try wp_auto
    wp_apply (wp_entRoC_GetIndex re (walEntCanon m)) $$ []
    · iexact Hc
    wp_apply (wp_entRoC_GetTerm re (walEntCanon m)) $$ []
    · iexact Hc
    have hdsl : ds.len = W64 (m.Data'.length : Int) := by word
    have hE : (⟨m.Index', m.Term', ds.len,
        List.foldl (tSaltStep m.Data') (W64 0) (List.range (min 8 m.Data'.length))⟩ : TEnt) =
        tFromRaftE m := by
      rw [hdsl]; rfl
    rw [hE]
    have hEs : uint.nat (tFromRaftE m).size' = m.Data'.length := by
      simp only [tFromRaftE]; word
    wp_apply (wp_entData (tFromRaftE m) (by rw [hEs]; have := Hdl.1; word)) as %wt ⟨Hwt, -⟩
    imod ownSlice_persist $$ Hwt with #Hwt
    ihave %Hwl := ownSlice_len $$ Hwt
    have hwl : (tEntData (tFromRaftE m)).length = m.Data'.length := by rw [tEntData_length', hEs]
    ihave HI2 : (∃ (i : w64),
        "i" ∷ i_ptr ↦ i ∗
        "e" ∷ e_ptr ↦ (if m.Data'.take (sint.nat i) = (tEntData (tFromRaftE m)).take (sint.nat i) then
          tFromRaftE m else { tFromRaftE m with size' := W64 0 }) ∗
        "%Hi2" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z ds.len⌝ : IProp GF) $$ [i e]
    · iexists W64 0
      rw [show sint.nat (W64 0) = 0 from rfl]
      simp only [List.take_zero, ite_true]
      iframe
      ipureintro; constructor <;> word
    wp_for HI2
    by_cases hlt2 : sint.Z i < sint.Z ds.len
    · first
        | rw [if_pos (show decide (sint.Z i < sint.Z ds.len) = true by simp [hlt2])]
        | rw [if_pos (show decide ((#(decide (sint.Z i < sint.Z ds.len)) : val) = #true) = true by simp [hlt2])]
      have hil2 : sint.nat i < m.Data'.length := by
        have : sint.nat i < sint.nat ds.len := by word
        omega
      obtain ⟨x, Hx⟩ : ∃ x, m.Data'[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hil2⟩
      obtain ⟨y, Hy⟩ : ∃ y, (tEntData (tFromRaftE m))[sint.nat i]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ds.len := ⟨Hi2.1, hlt2⟩
      have hb3 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z wt.len := ⟨Hi2.1, by word⟩
      icases ownSlice_elem_acc (sint.Z i) x ds DFrac.discard m.Data' Hi2.1
        (by simpa [sint.nat] using Hx) $$ Hds with ⟨Hxv, -⟩
      icases ownSlice_elem_acc (sint.Z i) y wt DFrac.discard _ Hi2.1
        (by simpa [sint.nat] using Hy) $$ Hwt with ⟨Hyv, -⟩
      wp_auto
      iterate 4 (try simp only [hb2, hb3, _root_.and_self, ↓reduceIte]; try wp_auto)
      have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      have hstep := take_succ_eq_iff Hx Hy
      wp_if_destruct
      · wp_for_post
        iframe
        iexists i + W64 1
        rw [hi1]
        have hxy : x = y := by simpa using Hif
        have hiff : (List.take (sint.nat i + 1) m.Data' = List.take (sint.nat i + 1) (tEntData (tFromRaftE m))) ↔
            (List.take (sint.nat i) m.Data' = List.take (sint.nat i) (tEntData (tFromRaftE m))) := by
          rw [hstep]; simp [hxy]
        simp only [hiff]
        iframe
        ipureintro; constructor <;> word
      · wp_for_post
        iframe
        iexists i + W64 1
        have hn : ¬ (List.take (sint.nat i + 1) m.Data' = List.take (sint.nat i + 1) (tEntData (tFromRaftE m))) := by
          rw [hstep]; intro h; exact Hif (by simpa using h.2)
        rw [hi1, if_neg hn]
        have hcur : ∀ v : TEnt, v = tFromRaftE m ∨ v = { tFromRaftE m with size' := W64 0 } →
            { v with size' := W64 0 } = { tFromRaftE m with size' := W64 0 } := by
          rintro v (rfl | rfl) <;> rfl
        rw [hcur (if List.take (sint.nat i) m.Data' = List.take (sint.nat i) (tEntData (tFromRaftE m)) then
            tFromRaftE m else { tFromRaftE m with size' := W64 0 })
          (by by_cases h : List.take (sint.nat i) m.Data' = List.take (sint.nat i) (tEntData (tFromRaftE m)) <;>
            simp [h])]
        iframe
        ipureintro; constructor <;> word
    · simp only [hlt2, decide_false, Bool.false_eq_true, ↓reduceIte, val_false_ne_true, _root_.decide_true,
    not_false_eq_true]
      have hin2 : sint.nat i = m.Data'.length := by
        have : sint.nat i = sint.nat ds.len := by word
        omega
      rw [hin2, List.take_length, show (tEntData (tFromRaftE m)).take m.Data'.length =
        tEntData (tFromRaftE m) by rw [← hwl, List.take_length]]
      wp_auto
      by_cases hdq : m.Data' = tEntData (tFromRaftE m)
      · have h1 : tFromRaft m = tFromRaftE m := by unfold tFromRaft; simp [hdq]
        rw [h1, if_pos hdq]; iapply HΦ; itrivial
      · have h1 : tFromRaft m = ⟨m.Index', m.Term', W64 0, tSaltOf m.Data'⟩ := by
          unfold tFromRaft; rw [if_neg hdq]; rfl
        rw [h1, if_neg hdq]; iapply HΦ; itrivial


end proof

end etcd_wal
end EtcdGrove
end Perennial
