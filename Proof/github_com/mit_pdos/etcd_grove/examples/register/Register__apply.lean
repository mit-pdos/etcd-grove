/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__apply.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.decode
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem Register.apply.wp_proof (wp_decode : register.decode.spec (GF := GF) (hG := hG)) :
    Register.apply.spec (GF := GF) (hG := hG) := by
  intro γr γp r id n st ap e
  wp_start as ⟨#Hrep, Hrun, #Hce⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  iunfold runOwn at Hrun
  iNamed Hrun
  -- the data of the entries applied so far and of `e`
  rw [← Hraft]
  imod node_committed_data γp.node id n (ap ++ [e]) ⊤ CoPset.subseteq_top $$ HisNode Hce
    with ⟨%ods', #Hods'⟩
  ihave %Hpre := entDataIs_list_prefix _ ap (ap ++ [e]) ods ods' (List.prefix_append _ _)
    $$ Hods Hods'
  ihave %Hl1 := BigSepL2.bigSepL2_length $$ Hods
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hods'
  obtain ⟨o, Ho⟩ : ∃ o, ods' = ods ++ [o] := by
    obtain ⟨rest, Hrest⟩ := Hpre
    subst Hrest
    simp only [List.length_append, List.length_singleton] at Hl2
    have h1 : rest.length = 1 := by omega
    match rest, h1 with
    | [o], _ => exact ⟨o, rfl⟩
    | [], h => simp at h
    | _ :: _ :: _, h => simp at h
  subst Ho
  ihave #He : entDataIs γp.node.raft e o $$ []
  · icases (BigSepL2.bigSepL2_snoc (Φ := fun _ e o => entDataIs (GF := GF) γp.node.raft e o)).1
      $$ Hods' with ⟨-, #He⟩
    iexact He
  -- what is kept when the entry changes nothing
  ihave Hkeep : iprop(r.[RRegister, go!"value"] ↦ v -∗ r.[RRegister, go!"applied"] ↦ mA -∗
      mA ↦$ A -∗ ⌜v = regFold (occStep (firstOcc ods) o) ∧
        AppliedOk A (occStep (firstOcc ods) o)⌝ -∗ runOwn γr r (ap ++ [e])) $$ []
  · iintro Hv HmA HA %Hocc
    unfold runOwn
    iexists v, mA, A, ods ++ [o]
    rw [← Hraft, firstOcc_snoc]
    iframe Hv HmA HA Hce Hods'
    ipureintro; exact Hocc
  wp_auto
  cases o with
  | none =>
    -- a leader's own entry: the zero slice, no operation
    iunfold entDataIs at He
    icases He with %Hz
    wp_if_destruct
    rotate_left
    · iapply HΦ
      iapply Hkeep $$ Hv HmA HA
      ipureintro; exact ⟨Hval, HA⟩
    ihave #Hnil : e.Data' ↦*□ ([] : List w8) $$ []
    · rw [Hz]; iapply ownSlice_nil
    wp_apply wp_decode e.Data' [] DFrac.discard $$ [$Hnil]
    iintro -
    simp only [decodeRet, show decodeOp ([] : List w8) = none from rfl]
    wp_auto
    iapply HΦ
    iapply Hkeep $$ Hv HmA HA
    ipureintro; exact ⟨Hval, HA⟩
  | some d =>
    ihave #He' := He
    iunfold entDataIs at He'
    icases He' with ⟨%Hz, #Hpd, #Hdep⟩
    imod node_entData_heap γp.node id n e d ⊤ CoPset.subseteq_top $$ HisNode He with #Hd
    wp_if_destruct
    rotate_left
    · exact absurd Hz.2 Hif
    wp_apply wp_decode e.Data' d DFrac.discard $$ [$Hd]
    iintro -
    -- the value after `d`, if `d` is skipped
    have Hskip : decodeOp d = none ∨ d ∈ firstOcc ods →
        v = regFold (occStep (firstOcc ods) (some d)) ∧
        AppliedOk A (occStep (firstOcc ods) (some d)) := by
      intro Hs
      refine ⟨?_, appliedOk_skip A _ d HA Hs⟩
      by_cases Hm : d ∈ firstOcc ods
      · rw [occStep_mem _ d Hm]; exact Hval
      · have Hd0 : decodeOp d = none := by rcases Hs with h | h; exact h; exact absurd h Hm
        rw [occStep_nmem _ d Hm, regFold_snoc, regApply_none _ _ Hd0]; exact Hval
    cases Hdec : decodeOp d with
    | none =>
      simp only [decodeRet, Hdec]
      wp_auto
      iapply HΦ
      iapply Hkeep $$ Hv HmA HA
      ipureintro; exact Hskip (.inl Hdec)
    | some x =>
      obtain ⟨rep, sq, k, val⟩ := x
      simp only [decodeRet, Hdec]
      wp_auto
      wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
      iNamed HR
      wp_apply wp_bytes_to_string e.Data' d DFrac.discard $$ [$Hd] as -
      wp_apply wp_map_lookup1 go.string go.bool mA A d (DFrac.own 1) $$ [$HA] as HA
      have Hdsome : (decodeOp d).isSome := by rw [Hdec]; rfl
      rw [show (zero_val Bool) = false from rfl, appliedOk_lookup A _ d HA Hdsome]
      wp_if_destruct
      · -- applied before: unlock, skip
        wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters]
        · inext
          unfold lockInv
          iexists ns, mW, W, c
          iframe
          ipureintro; exact ⟨Hc, HWdom⟩
        iapply HΦ
        iapply Hkeep $$ Hv HmA HA
        ipureintro; exact Hskip (.inr Hif)
      have Hnew := Hif
      -- the first occurrence of `d`: the operation applied
      iclear Hkeep
      ihave Hfin : iprop(r.[RRegister, go!"value"] ↦ regApply v d -∗
          r.[RRegister, go!"applied"] ↦ mA -∗ mA ↦$ A.insert d true -∗
          runOwn γr r (ap ++ [e])) $$ []
      · iintro Hv HmA HA'
        unfold runOwn
        iexists regApply v d, mA, A.insert d true, ods ++ [some d]
        rw [← Hraft, firstOcc_snoc, occStep_nmem _ d Hnew, regFold_snoc, ← Hval]
        iframe Hv HmA HA' Hce Hods'
        ipureintro; exact ⟨rfl, appliedOk_insert A _ d HA Hnew Hdsome⟩
      wp_apply wp_bytes_to_string e.Data' d DFrac.discard $$ [$Hd] as -
      wp_apply wp_mapInsert go.string mA A d true $$ [$HA] as HA
      wp_if_destruct
      · -- a `Put`
        ihave Hv : r.[RRegister, go!"value"] ↦ regApply v d $$ [Hv]
        · simp only [regApply, Hdec]
          rw [if_pos (show W8 1 = opPutB from rfl)]
          iexact Hv
        wp_if_destruct
        · -- this replica's operation: its waiter, if any
          wp_apply wp_map_lookup2 go.uint64 (go.GoType.ChannelType go.ChanDir.sendrecv go.string) mW W sq
            (DFrac.own 1) $$ [$HW] as HW
          cases HWs : W !! sq with
          | none =>
            simp only [Option.getD_none, Option.isSome_none, decide_false, Bool.false_eq_true]
            wp_auto
            wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters]
            · inext
              unfold lockInv
              iexists ns, mW, W, c
              iframe
              ipureintro; exact ⟨Hc, HWdom⟩

            iapply HΦ
            iapply Hfin $$ Hv HmA HA
          | some ch =>
            simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
            wp_auto
            wp_apply wp_mapDelete mW W sq go.uint64 (go.GoType.ChannelType go.ChanDir.sendrecv go.string)
              $$ [$HW] as HW
            icases (BigSepM.bigSepM_delete (Φ := fun s ch => waiterOk (GF := GF) γr id s ch) HWs).1
              $$ Hwaiters with ⟨Hw, Hwaiters⟩
            iunfold waiterOk at Hw
            icases Hw with ⟨%d0, %γh, #Hmint, #Hho, Hprod⟩
            -- the waiter's operation is `d`: both are minted at `(id, sq)`
            have Hkey : opKey d = some (rep, sq) := by simp [opKey, Hdec]
            imod reg_deposited_minted γr d d0 (rep, sq) ⊤ CoPset.subseteq_top
              (by rw [show (⊤ : CoPset) \ ↑regN = ⊤ \ ↑regN from rfl]; exact raftN_regN) Hkey
              $$ Hinv [] [] [] with %Hd0
            · rw [← Hraft]; open_node HisNode; iexact Hcinv
            · rw [← Hraft]; iexact Hdep
            · rw [Hif]; iexact Hmint
            subst Hd0
            wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters]
            · inext
              unfold lockInv
              iexists ns, mW, GMap.delete sq W, c
              iframe
              ipureintro
              refine ⟨Hc, fun s ch' Hs => HWdom s ch' ?_⟩
              by_cases Hss : s = sq
              · subst Hss; rw [GMap.lookup_delete_eq] at Hs; cases Hs
              · rwa [GMap.lookup_delete_ne _ (Ne.symm Hss)] at Hs
            wp_apply wp_handoff_send (t := go.string) γh ch (waitP γr d0) iprop(True) iprop(False)
              (regApply v d0) $$ [$Hho $Hprod]
            · isplitl
              · unfold waitP
                iexists ap ++ [e], ods ++ [some d0], ods.length
                rw [← Hraft]
                iframe Hce Hods'
                ipureintro
                refine ⟨by simp, ?_, ?_⟩
                · rw [List.take_left' rfl]; exact Hnew
                · rw [List.take_left' rfl, regFold_snoc, ← Hval]
              · itrivial
            iintro -
            wp_auto
            iapply HΦ
            iapply Hfin $$ Hv HmA HA
        · -- another replica's operation
          wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters]
          · inext
            unfold lockInv
            iexists ns, mW, W, c
            iframe
            ipureintro; exact ⟨Hc, HWdom⟩

          iapply HΦ
          iapply Hfin $$ Hv HmA HA
      · ihave Hv : r.[RRegister, go!"value"] ↦ regApply v d $$ [Hv]
        · simp only [regApply, Hdec]
          rw [if_neg (by unfold opPutB; exact Hif)]
          iexact Hv
        wp_if_destruct
        · -- this replica's operation: its waiter, if any
          wp_apply wp_map_lookup2 go.uint64 (go.GoType.ChannelType go.ChanDir.sendrecv go.string) mW W sq
            (DFrac.own 1) $$ [$HW] as HW
          cases HWs : W !! sq with
          | none =>
            simp only [Option.getD_none, Option.isSome_none, decide_false, Bool.false_eq_true]
            wp_auto
            wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters]
            · inext
              unfold lockInv
              iexists ns, mW, W, c
              iframe
              ipureintro; exact ⟨Hc, HWdom⟩

            iapply HΦ
            iapply Hfin $$ Hv HmA HA
          | some ch =>
            simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
            wp_auto
            wp_apply wp_mapDelete mW W sq go.uint64 (go.GoType.ChannelType go.ChanDir.sendrecv go.string)
              $$ [$HW] as HW
            icases (BigSepM.bigSepM_delete (Φ := fun s ch => waiterOk (GF := GF) γr id s ch) HWs).1
              $$ Hwaiters with ⟨Hw, Hwaiters⟩
            iunfold waiterOk at Hw
            icases Hw with ⟨%d0, %γh, #Hmint, #Hho, Hprod⟩
            -- the waiter's operation is `d`: both are minted at `(id, sq)`
            have Hkey : opKey d = some (rep, sq) := by simp [opKey, Hdec]
            imod reg_deposited_minted γr d d0 (rep, sq) ⊤ CoPset.subseteq_top
              (by rw [show (⊤ : CoPset) \ ↑regN = ⊤ \ ↑regN from rfl]; exact raftN_regN) Hkey
              $$ Hinv [] [] [] with %Hd0
            · rw [← Hraft]; open_node HisNode; iexact Hcinv
            · rw [← Hraft]; iexact Hdep
            · rw [Hif]; iexact Hmint
            subst Hd0
            wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters]
            · inext
              unfold lockInv
              iexists ns, mW, GMap.delete sq W, c
              iframe
              ipureintro
              refine ⟨Hc, fun s ch' Hs => HWdom s ch' ?_⟩
              by_cases Hss : s = sq
              · subst Hss; rw [GMap.lookup_delete_eq] at Hs; cases Hs
              · rwa [GMap.lookup_delete_ne _ (Ne.symm Hss)] at Hs
            wp_apply wp_handoff_send (t := go.string) γh ch (waitP γr d0) iprop(True) iprop(False)
              (regApply v d0) $$ [$Hho $Hprod]
            · isplitl
              · unfold waitP
                iexists ap ++ [e], ods ++ [some d0], ods.length
                rw [← Hraft]
                iframe Hce Hods'
                ipureintro
                refine ⟨by simp, ?_, ?_⟩
                · rw [List.take_left' rfl]; exact Hnew
                · rw [List.take_left' rfl, regFold_snoc, ← Hval]
              · itrivial
            iintro -
            wp_auto
            iapply HΦ
            iapply Hfin $$ Hv HmA HA
        · -- another replica's operation
          wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters]
          · inext
            unfold lockInv
            iexists ns, mW, W, c
            iframe
            ipureintro; exact ⟨Hc, HWdom⟩

          iapply HΦ
          iapply Hfin $$ Hv HmA HA

end proof

end register
end EtcdGrove
end Perennial
