/-
The proof of `service.Store.Apply` (adapted from dsverify-lab's hr3 `store__Apply.lean`, 241f27e):
the register moves past the command, the frontier with it if it was at the FSM's prefix
(`frontier_apply`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.Store__Apply
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

theorem github_com.hashicorp.raft.examples.hraftnet.service.Store.Apply.wp_proof
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.service.Store.Apply.spec (GF := GF) (hG := hG) := by
  intro γ fc alb i s l k0 k e
  wp_start as ⟨#Hst, Hown, #Hl, %Hk, #Hc, #Hdur, #Hnc⟩
  unfold isStore
  icases Hst with ⟨#Hlock, #Hfr, #Hls, #Hdb⟩
  unfold logPtr logIs
  icases Hl with ⟨%lv, #Hlv, %Hlvk, #Hdata, %ext, #Hext⟩
  ihave Hlv2 := Hlv
  iStructNamed Hlv2
  wp_auto
  wp_apply (lc := 1) wp_with_defer as %defer Hdefer
  wp_apply wp_Mutex_Lock $$ [$Hlock] as ⟨Hlocked, Hinv⟩
  unfold storeInv fsmOwn
  icases Hinv with ⟨%es, #Hpre, #Hflb, Halb2, Hpres, Hval, Hidx, %Hes⟩
  unfold durBound
  imod Hdb $$ %k Hdur with %Hk62
  ihave %Hag := monoNatAuthOwn_agree _ _ _ _ _ $$ Hown Halb2
  have Hes0 : es.length = k0 := Hag.2.symm
  subst Hes0
  ihave Halb := monoNat_halves _ _ $$ [Hown Halb2]
  · iframe
  imod mono_nat_own_update k (by omega) $$ Halb with ⟨Halb, #Hlb⟩
  ihave ⟨Halb, Halb2⟩ := monoNat_split _ _ $$ Halb
  icases noCmdBetween_list γ es.length k $$ Hnc with ⟨%ns, %Hns, #Hns⟩
  have Hlen' : (es ++ ns ++ [e]).length = k := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  ihave #Hpre' : cIdxs γ (es ++ ns ++ [e]) $$ []
  · iapply cIdxs_append γ (es ++ ns) [e]
    isplitl
    · iapply cIdxs_append γ es ns
      iframe #
    · iapply BigSepL.bigSepL_singleton.2
      rw [List.length_append, Hns.1, show es.length + (k - (es.length + 1)) + 1 + 0 = k by omega]
      iexact Hc
  ihave Hfa := frontier_apply γ fc es ns e Hns.2 Hk.2 $$ [Hlc1]
  · iframe Hlc1; iframe #
    rw [Hlen']
    iexact Hnc
  imod Hfa with #Hflb'
  obtain ⟨hk1, -, -⟩ := Hlvk
  have hidxw : lv.Index' = W64 ((es ++ ns ++ [e]).length : Int) := by rw [Hlen', ← hk1]; word
  have hlastc : lastCmd (es ++ ns ++ [e]) := lastCmd_snoc _ e Hk.2
  have hI62 : uint.nat lv.Index' < 2 ^ 62 := by omega
  have hIw : W64 (uint.nat lv.Index' : Int) = lv.Index' := by word
  have Hk' : k = (es ++ ns).length + 1 := by simp only [List.length_append]; omega
  ihave %Hdlen := ownSlice_len $$ Hdata
  wp_auto
  simp only [CmdHdr, CmdPut]
  wp_if_destruct
  · have hlen9 : 9 ≤ e.data.length := by have := Hdlen.1; word
    obtain ⟨b0, rest, hbr⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega) :
      e.data ≠ [])
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z lv.Data'.len by
      have := Hdlen.1; constructor <;> word)]
    wp_apply (wp_load_slice_index lv.Data' (sint.Z (W64 0)) e.data DFrac.discard b0 (by decide))
      $$ [$Hdata] as -
    · ipureintro; rw [hbr]; rfl
    wp_if_destruct
    · ihave %Hwf := ownSlice_wf _ _ _ $$ Hdata
      have hb2 : 0 ≤ sint.Z (W64 9) ∧ sint.Z (W64 9) ≤ sint.Z lv.Data'.len ∧
          sint.Z lv.Data'.len ≤ sint.Z lv.Data'.cap := by
        have := Hdlen.1; refine ⟨by decide, ?_, Hwf.2⟩; word
      rw [ite_eq_left hb2]
      icases (ownSlice_slice (W64 9) lv.Data'.len lv.Data' DFrac.discard e.data
        ⟨hb2.1, hb2.2.1, Int.le_refl _⟩).1 $$ Hdata with ⟨-, #Hs2, -⟩
      wp_apply (wp_bytes_to_string _ _ DFrac.discard) $$ [$Hs2] as -
      have hsub : subslice (sint.nat (W64 9)) (sint.nat lv.Data'.len) e.data = putVal e.data := by
        unfold subslice putVal
        rw [← Hdlen.1, List.take_length]
        rfl
      have hput : isPut e.data := ⟨hlen9, by rw [hbr]; rfl⟩
      have hreg : regOf (es ++ ns ++ [e]) = some (putVal e.data) := by
        rw [regOf_step es ns e Hns.2]; simp [applyEnt, Hk.2, hput]
      have hresp : respAt (es ++ ns ++ [e]) = result.mk false [] := by
        rw [respAt_step es ns e Hns.2]; simp [respOf, hput]
      wp_apply wp_Mutex_Unlock $$ [$Hlock $Hlocked Halb2 Hpres Hval Hidx]
      · inext; iexists es ++ ns ++ [e]; rw [hreg, Hlen', ← hk1]
        rw [hIw]
        simp only [Option.isSome_some, Option.getD_some]
        rw [← hsub]
        iframe; iframe #; ipureintro; exact ⟨hI62, hlastc⟩
      try wp_auto
      iapply HΦ
      unfold respP appliedLb
      iframe Halb
      iexists es ++ ns ++ [e]
      iframe #
      ipureintro
      exact ⟨Hlen', by rw [hresp]; rfl⟩
    · have hnp : ¬ isPut e.data := by
        intro h; apply Hif; have := h.2; rw [hbr] at this; simpa using this
      have hreg : regOf (es ++ ns ++ [e]) = regOf es := by
        rw [regOf_step es ns e Hns.2]; simp [applyEnt, hnp]
      have hresp : respAt (es ++ ns ++ [e]) = result.mk (regOf es).isSome ((regOf es).getD []) := by
        rw [respAt_step es ns e Hns.2]; simp [respOf, hnp, resOf]
      wp_apply wp_Mutex_Unlock $$ [$Hlock $Hlocked Halb2 Hpres Hval Hidx]
      · inext; iexists es ++ ns ++ [e]; rw [hreg, Hlen', ← hk1]
        rw [hIw]
        iframe; iframe #; ipureintro; exact ⟨hI62, hlastc⟩
      try wp_auto
      iapply HΦ
      unfold respP appliedLb
      iframe Halb
      iexists es ++ ns ++ [e]
      iframe #
      ipureintro
      exact ⟨Hlen', by rw [hresp]⟩
  · have hnp : ¬ isPut e.data := by
      intro h; apply Hif; have := h.1; have := Hdlen.1; word
    have hreg : regOf (es ++ ns ++ [e]) = regOf es := by
      rw [regOf_step es ns e Hns.2]; simp [applyEnt, hnp]
    have hresp : respAt (es ++ ns ++ [e]) = result.mk (regOf es).isSome ((regOf es).getD []) := by
      rw [respAt_step es ns e Hns.2]; simp [respOf, hnp, resOf]
    wp_apply wp_Mutex_Unlock $$ [$Hlock $Hlocked Halb2 Hpres Hval Hidx]
    · inext; iexists es ++ ns ++ [e]; rw [hreg, Hlen', ← hk1]
      rw [hIw]
      iframe; iframe #; ipureintro; exact ⟨hI62, hlastc⟩
    try wp_auto
    iapply HΦ
    unfold respP appliedLb
    iframe Halb
    iexists es ++ ns ++ [e]
    iframe #
    ipureintro
    exact ⟨Hlen', by rw [hresp]⟩

end proof

end Perennial
