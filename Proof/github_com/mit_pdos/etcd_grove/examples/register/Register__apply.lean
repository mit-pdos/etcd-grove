/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__apply.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): the entry is read through its getters
(`GetType`, `GetData`: the record's type and a read-only slice of its bytes, D6).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.decode
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
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

theorem Register.apply.wp_proof (wp_decode : register.decode.spec (GF := GF) (hG := hG))
    (wp_Entry_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Entry_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG)) :
    Register.apply.spec (GF := GF) (hG := hG) := by
  intro γr γp r id n st ap e em
  wp_start as ⟨#Hrep, Hrun, #He, #Hce⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  iunfold runOwn at Hrun
  iNamed Hrun
  -- the data of the entries applied so far and of `em`
  rw [← Hraft]
  imod node_committed_data γp.node id n (ap ++ [em]) ⊤ CoPset.subseteq_top $$ HisNode Hce
    with ⟨%ods', #Hods'⟩
  ihave %Hpre := entDataIs_list_prefix _ ap (ap ++ [em]) ods ods' (List.prefix_append _ _)
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
  ihave #Hem : entDataIs γp.node.raft em o $$ []
  · icases (BigSepL2.bigSepL2_snoc (Φ := fun _ e o => entDataIs (GF := GF) γp.node.raft e o)).1
      $$ Hods' with ⟨-, #Hem⟩
    iexact Hem
  -- what is kept when the entry changes nothing
  ihave Hkeep : iprop(r.[RRegister, go!"value"] ↦ v -∗ r.[RRegister, go!"applied"] ↦ mA -∗
      mA ↦$ A -∗ ⌜v = regFold (occStep (firstOcc ods) o) ∧
        AppliedOk A (occStep (firstOcc ods) o)⌝ -∗ runOwn γr r (ap ++ [em])) $$ []
  · iintro Hv HmA HA %Hocc
    unfold runOwn
    iexists v, mA, A, ods ++ [o]
    rw [← Hraft, firstOcc_snoc]
    iframe Hv HmA HA Hce Hods'
    ipureintro; exact Hocc
  wp_auto
  -- `e.GetType() != pb.EntryNormal`
  wp_apply wp_Entry_GetType.1 e DFrac.discard em $$ [$Hpbinit $He] as -
  cases o with
  | none =>
    -- a leader's own entry (no bytes) or (2026-10-13) an entry of another type (a conf
    -- change): no operation
    iunfold entDataIs at Hem
    icases Hem with (%Hz | %Hty)
    rotate_left
    · -- not a normal entry: `apply` returns at once
      wp_if_destruct
      · exact absurd Hif Hty.1
      · iapply HΦ
        iapply Hkeep $$ Hv HmA HA
        ipureintro; exact ⟨Hval, HA⟩
    wp_if_destruct
    rotate_left
    · iapply HΦ
      iapply Hkeep $$ Hv HmA HA
      ipureintro; exact ⟨Hval, HA⟩
    wp_apply wp_Entry_GetData.1 e DFrac.discard em $$ [$Hpbinit $He] as %ds ⟨#Hd, -⟩
    wp_apply wp_decode ds em.Data' DFrac.discard $$ [$Hd]
    iintro -
    rw [Hz.2]
    simp only [decodeRet, show decodeOp ([] : List w8) = none from rfl]
    wp_auto
    iapply HΦ
    iapply Hkeep $$ Hv HmA HA
    ipureintro; exact ⟨Hval, HA⟩
  | some d =>
    ihave #Hem' := Hem
    iunfold entDataIs at Hem'
    icases Hem' with ⟨%Hz, #Hdep⟩
    obtain ⟨Hz1, Hdne, Hty0⟩ := Hz
    subst Hz1
    wp_if_destruct
    rotate_left
    · exact absurd Hty0 Hif
    wp_apply wp_Entry_GetData.1 e DFrac.discard em $$ [$Hpbinit $He] as %ds ⟨#Hd, -⟩
    wp_apply wp_decode ds em.Data' DFrac.discard $$ [$Hd]
    iintro -
    -- the value after `em.Data'`, if `em.Data'` is skipped
    have Hskip : decodeOp em.Data' = none ∨ em.Data' ∈ firstOcc ods →
        v = regFold (occStep (firstOcc ods) (some em.Data')) ∧
        AppliedOk A (occStep (firstOcc ods) (some em.Data')) := by
      intro Hs
      refine ⟨?_, appliedOk_skip A _ em.Data' HA Hs⟩
      by_cases Hm : em.Data' ∈ firstOcc ods
      · rw [occStep_mem _ em.Data' Hm]; exact Hval
      · have Hd0 : decodeOp em.Data' = none := by rcases Hs with h | h; exact h; exact absurd h Hm
        rw [occStep_nmem _ em.Data' Hm, regFold_snoc, regApply_none _ _ Hd0]; exact Hval
    cases Hdec : decodeOp em.Data' with
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
      -- `string(e.GetData())`
      wp_apply wp_Entry_GetData.1 e DFrac.discard em $$ [$Hpbinit $He] as %ds1 ⟨#Hd1, -⟩
      wp_apply wp_bytes_to_string ds1 em.Data' DFrac.discard $$ [$Hd1] as -
      wp_apply wp_map_lookup1 go.string go.bool mA A em.Data' (DFrac.own 1) $$ [$HA] as HA
      have Hdsome : (decodeOp em.Data').isSome := by rw [Hdec]; rfl
      rw [show (zero_val Bool) = false from rfl, appliedOk_lookup A _ em.Data' HA Hdsome]
      wp_if_destruct
      · -- applied before: unlock, skip
        wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters Hrds]
        · inext
          unfold lockInv
          iexists ns, mW, W, c
          iframe
          ipureintro; exact ⟨Hc, HWdom⟩
        iapply HΦ
        iapply Hkeep $$ Hv HmA HA
        ipureintro; exact Hskip (.inr Hif)
      have Hnew := Hif
      -- the first occurrence of `em.Data'`: the operation applied
      iclear Hkeep
      ihave Hfin : iprop(r.[RRegister, go!"value"] ↦ regApply v em.Data' -∗
          r.[RRegister, go!"applied"] ↦ mA -∗ mA ↦$ A.insert em.Data' true -∗
          runOwn γr r (ap ++ [em])) $$ []
      · iintro Hv HmA HA'
        unfold runOwn
        iexists regApply v em.Data', mA, A.insert em.Data' true, ods ++ [some em.Data']
        rw [← Hraft, firstOcc_snoc, occStep_nmem _ em.Data' Hnew, regFold_snoc, ← Hval]
        iframe Hv HmA HA' Hce Hods'
        ipureintro; exact ⟨rfl, appliedOk_insert A _ em.Data' HA Hnew Hdsome⟩
      wp_apply wp_Entry_GetData.1 e DFrac.discard em $$ [$Hpbinit $He] as %ds2 ⟨#Hd2, -⟩
      wp_apply wp_bytes_to_string ds2 em.Data' DFrac.discard $$ [$Hd2] as -
      wp_apply wp_mapInsert go.string mA A em.Data' true $$ [$HA] as HA
      wp_if_destruct
      · -- a `Put`
        ihave Hv : r.[RRegister, go!"value"] ↦ regApply v em.Data' $$ [Hv]
        · simp only [regApply, Hdec]
          rw [ite_eq_left (show W8 1 = opPutB from rfl)]
          iexact Hv
        wp_if_destruct
        · -- this replica's operation: its waiter, if any
          wp_apply wp_map_lookup2 go.uint64 (go.GoType.ChannelType go.ChanDir.sendrecv go.string) mW W sq
            (DFrac.own 1) $$ [$HW] as HW
          cases HWs : W !! sq with
          | none =>
            simp only [Option.getD_none, Option.isSome_none, decide_false, Bool.false_eq_true]
            wp_auto
            wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters Hrds]
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
            -- the waiter's operation is `em.Data'`: both are minted at `(id, sq)`
            have Hkey : opKey em.Data' = some (rep, sq) := by simp [opKey, Hdec]
            imod reg_deposited_minted γr em.Data' d0 (rep, sq) ⊤ CoPset.subseteq_top
              (by rw [show (⊤ : CoPset) \ ↑regN = ⊤ \ ↑regN from rfl]; exact raftN_regN) Hkey
              $$ Hinv [] [] [] with %Hd0
            · rw [← Hraft]; open_node HisNode; iexact Hcinv
            · rw [← Hraft]; iexact Hdep
            · rw [Hif]; iexact Hmint
            subst Hd0
            wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters Hrds]
            · inext
              unfold lockInv
              iexists ns, mW, GMap.delete sq W, c
              iframe
              ipureintro
              refine ⟨Hc, fun s ch' Hs => HWdom s ch' ?_⟩
              by_cases Hss : s = sq
              · subst Hss; rw [GMap.lookup_delete_eq] at Hs; cases Hs
              · rwa [GMap.lookup_delete_ne _ (Ne.symm Hss)] at Hs
            wp_apply wp_handoff_send (t := go.string) γh ch (waitP γr em.Data') iprop(True) iprop(False)
              (regApply v em.Data') $$ [$Hho $Hprod]
            · isplitl
              · unfold waitP
                iexists ap ++ [em], ods ++ [some em.Data'], ods.length
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
          wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters Hrds]
          · inext
            unfold lockInv
            iexists ns, mW, W, c
            iframe
            ipureintro; exact ⟨Hc, HWdom⟩

          iapply HΦ
          iapply Hfin $$ Hv HmA HA
      · ihave Hv : r.[RRegister, go!"value"] ↦ regApply v em.Data' $$ [Hv]
        · simp only [regApply, Hdec]
          rw [ite_eq_right (by unfold opPutB; exact Hif)]
          iexact Hv
        wp_if_destruct
        · -- this replica's operation: its waiter, if any
          wp_apply wp_map_lookup2 go.uint64 (go.GoType.ChannelType go.ChanDir.sendrecv go.string) mW W sq
            (DFrac.own 1) $$ [$HW] as HW
          cases HWs : W !! sq with
          | none =>
            simp only [Option.getD_none, Option.isSome_none, decide_false, Bool.false_eq_true]
            wp_auto
            wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters Hrds]
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
            -- the waiter's operation is `em.Data'`: both are minted at `(id, sq)`
            have Hkey : opKey em.Data' = some (rep, sq) := by simp [opKey, Hdec]
            imod reg_deposited_minted γr em.Data' d0 (rep, sq) ⊤ CoPset.subseteq_top
              (by rw [show (⊤ : CoPset) \ ↑regN = ⊤ \ ↑regN from rfl]; exact raftN_regN) Hkey
              $$ Hinv [] [] [] with %Hd0
            · rw [← Hraft]; open_node HisNode; iexact Hcinv
            · rw [← Hraft]; iexact Hdep
            · rw [Hif]; iexact Hmint
            subst Hd0
            wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters Hrds]
            · inext
              unfold lockInv
              iexists ns, mW, GMap.delete sq W, c
              iframe
              ipureintro
              refine ⟨Hc, fun s ch' Hs => HWdom s ch' ?_⟩
              by_cases Hss : s = sq
              · subst Hss; rw [GMap.lookup_delete_eq] at Hs; cases Hs
              · rwa [GMap.lookup_delete_ne _ (Ne.symm Hss)] at Hs
            wp_apply wp_handoff_send (t := go.string) γh ch (waitP γr em.Data') iprop(True) iprop(False)
              (regApply v em.Data') $$ [$Hho $Hprod]
            · isplitl
              · unfold waitP
                iexists ap ++ [em], ods ++ [some em.Data'], ods.length
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
          wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters Hrds]
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
