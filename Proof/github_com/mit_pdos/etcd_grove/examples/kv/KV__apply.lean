/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__apply.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): the entry is read through its getters
(`GetType`, `GetData`: the record's type and a read-only slice of its bytes, D6).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.decode
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.LemmasOps
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

set_option hygiene false in
/-- `apply` from `v := r.kv[key]` on (2026-10-22: the answer `v` recorded in the table of the
operations applied, `r.applied[...] = v`; then the waiter's removal and its handoff), with the
new map `Kn` (`HvalN`) in `HK`. -/
local macro "apply_rest" : tactic => `(tactic| (
    have HvK : (Kn !! key).getD [] = kvFold (firstOcc ods ++ [em.Data']) (dkey em.Data') := by
      rw [kvFold_snoc, HvalN, show dkey em.Data' = key by simp [dkey, Hdec]]
    wp_apply wp_map_lookup1 go.string go.string mK Kn key (DFrac.own 1) $$ [$(frameH `HK)] as HK
    try wp_auto
    wp_apply wp_Entry_GetData.1 e DFrac.discard em $$ [$(frameH `Hpbinit) $(frameH `He)]
      as %ds2 ⟨#Hd2, -⟩
    wp_apply wp_bytes_to_string ds2 em.Data' DFrac.discard $$ [$(frameH `Hd2)] as -
    wp_apply wp_mapInsert go.string mA A em.Data' ((Kn !! key).getD (zero_val (List w8)))
      $$ [$(frameH `HA)] as HA
    try wp_auto
    wp_if_destruct
    · -- this replica's operation: its waiter, if any
      wp_apply wp_map_lookup2 go.uint64 (go.GoType.ChannelType go.ChanDir.sendrecv go.string) mW W sq
        (DFrac.own 1) $$ [$(frameH `HW)] as HW
      cases HWs : W !! sq with
      | none =>
        simp only [Option.getD_none, Option.isSome_none, decide_false, Bool.false_eq_true]
        try wp_auto
        wp_apply sync.Mutex.wp_Unlock _ _ $$ [$(frameH `Hmu) $(frameH `Hlocked) Hns HmW HW Hseq Hwaiters Hrds]
        · inext
          unfold lockInv
          iexists ns, mW, W
          iframe
          ipureintro; exact HWdom
        try wp_auto
        iapply HΦ
        iapply Hfin $$ %Kn %HvalN HmK HK HmA HA
      | some ch =>
        simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
        try wp_auto
        wp_apply wp_mapDelete mW W sq go.uint64 (go.GoType.ChannelType go.ChanDir.sendrecv go.string)
          $$ [$(frameH `HW)] as HW
        icases (BigSepM.bigSepM_delete (Φ := fun s ch => waiterOk (GF := GF) γr id s ch) HWs).1
          $$ Hwaiters with ⟨Hw, Hwaiters⟩
        iunfold waiterOk at Hw
        icases Hw with ⟨%d0, %γh, #Hmint, #Hho, Hprod⟩
        -- the waiter's operation is `em.Data'`: both are minted at `(id, sq)`
        have Hkey : opKey em.Data' = some (rep, sq) := by simp [opKey, Hdec]
        imod kv_deposited_minted γr em.Data' d0 (rep, sq) ⊤ CoPset.subseteq_top
          (by rw [show (⊤ : CoPset) \ ↑rkvN = ⊤ \ ↑rkvN from rfl]; exact raftN_regN) Hkey
          $$ Hinv [] [] [] with %Hd0
        · rw [← Hraft]; iapply isNode_commitInv $$ HisNode
        · rw [← Hraft]; iexact Hdep
        · rw [Hif]; iexact Hmint
        subst Hd0
        try wp_auto
        wp_apply sync.Mutex.wp_Unlock _ _ $$ [$(frameH `Hmu) $(frameH `Hlocked) Hns HmW HW Hseq Hwaiters Hrds]
        · inext
          unfold lockInv
          iexists ns, mW, GMap.delete sq W
          iframe
          ipureintro
          refine fun s ch' Hs => HWdom s ch' ?_
          by_cases Hss : s = sq
          · subst Hss; rw [GMap.lookup_delete_eq] at Hs; cases Hs
          · rwa [GMap.lookup_delete_ne _ (Ne.symm Hss)] at Hs
        try wp_auto
        wp_apply wp_handoff_send (t := go.string) γh ch (waitP γr em.Data') iprop(True) iprop(False)
          ((Kn !! key).getD (zero_val (List w8))) $$ [$(frameH `Hho) $(frameH `Hprod)]
        · isplitl
          · unfold waitP
            iexists ap ++ [em], ods ++ [some em.Data'], ods.length
            rw [← Hraft]
            iframe Hce Hods'
            ipureintro
            refine ⟨by simp, ?_, ?_⟩
            · rw [List.take_left' rfl]; exact Hnew
            · rw [List.take_left' rfl]; exact HvK
          · itrivial
        iintro -
        try wp_auto
        iapply HΦ
        iapply Hfin $$ %Kn %HvalN HmK HK HmA HA
    · -- another replica's operation
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock _ _ $$ [$(frameH `Hmu) $(frameH `Hlocked) Hns HmW HW Hseq Hwaiters Hrds]
      · inext
        unfold lockInv
        iexists ns, mW, W
        iframe
        ipureintro; exact HWdom
      try wp_auto
      iapply HΦ
      iapply Hfin $$ %Kn %HvalN HmK HK HmA HA
  ))

theorem KV.apply.wp_proof (wp_decode : kv.decode.spec (GF := GF) (hG := hG))
    (wp_Entry_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Entry_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG)) :
    KV.apply.spec (GF := GF) (hG := hG) := by
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
  ihave Hkeep : iprop(r.[RKV, go!"kv"] ↦ mK -∗ mK ↦$ K -∗ r.[RKV, go!"applied"] ↦ mA -∗
      mA ↦$ A -∗ ⌜(∀ k, (K !! k).getD [] = kvFold (occStep (firstOcc ods) o) k) ∧
        AppliedOk A (occStep (firstOcc ods) o)⌝ -∗ runOwn γr r (ap ++ [em])) $$ []
  · iintro HmK HK HmA HA %Hocc
    unfold runOwn
    iexists mK, K, mA, A, ods ++ [o]
    rw [← Hraft, firstOcc_snoc]
    iframe HmK HK HmA HA Hce Hods'
    ipureintro; exact Hocc
  wp_auto
  -- `e.GetType() != pb.EntryNormal`
  wp_apply wp_Entry_GetType.1 e DFrac.discard em $$ [$Hpbinit $He] as -
  cases o with
  | none =>
    -- a leader's own entry (no bytes) or an entry of another type (a conf change): no
    -- operation
    ihave Hem := entDataIs_prop γp.node.raft em none $$ Hem
    iunfold propDataIs at Hem
    icases Hem with (%Hz | %Hty)
    rotate_left
    · -- not a normal entry: `apply` returns at once
      wp_if_destruct
      · exact absurd Hif Hty.1
      · iapply HΦ
        iapply Hkeep $$ HmK HK HmA HA
        ipureintro; exact ⟨Hval, HA⟩
    wp_if_destruct
    rotate_left
    · iapply HΦ
      iapply Hkeep $$ HmK HK HmA HA
      ipureintro; exact ⟨Hval, HA⟩
    wp_apply wp_Entry_GetData.1 e DFrac.discard em $$ [$Hpbinit $He] as %ds ⟨#Hd, -⟩
    wp_apply wp_decode ds em.Data' DFrac.discard $$ [$Hd]
    iintro -
    rw [Hz.2]
    simp only [decodeRet, show decodeOp ([] : List w8) = none from rfl]
    wp_auto
    iapply HΦ
    iapply Hkeep $$ HmK HK HmA HA
    ipureintro; exact ⟨Hval, HA⟩
  | some d =>
    ihave #Hem' := Hem
    ihave Hem' := entDataIs_prop γp.node.raft em (some d) $$ Hem'
    iunfold propDataIs at Hem'
    icases Hem' with ⟨%Hz, #Hdep⟩
    obtain ⟨Hz1, Hdne, Hty0⟩ := Hz
    subst Hz1
    wp_if_destruct
    rotate_left
    · exact absurd Hty0 Hif
    wp_apply wp_Entry_GetData.1 e DFrac.discard em $$ [$Hpbinit $He] as %ds ⟨#Hd, -⟩
    wp_apply wp_decode ds em.Data' DFrac.discard $$ [$Hd]
    iintro -
    -- the store after `em.Data'`, if `em.Data'` is skipped
    have Hskip : decodeOp em.Data' = none ∨ em.Data' ∈ firstOcc ods →
        (∀ k, (K !! k).getD [] = kvFold (occStep (firstOcc ods) (some em.Data')) k) ∧
        AppliedOk A (occStep (firstOcc ods) (some em.Data')) := by
      intro Hs
      refine ⟨?_, appliedOk_skip A _ em.Data' HA Hs⟩
      by_cases Hm : em.Data' ∈ firstOcc ods
      · rw [occStep_mem _ em.Data' Hm]; exact Hval
      · have Hd0 : decodeOp em.Data' = none := by rcases Hs with h | h; exact h; exact absurd h Hm
        rw [occStep_nmem _ em.Data' Hm, kvFold_snoc, kvApply_none _ _ Hd0]; exact Hval
    cases Hdec : decodeOp em.Data' with
    | none =>
      simp only [decodeRet, Hdec]
      wp_auto
      iapply HΦ
      iapply Hkeep $$ HmK HK HmA HA
      ipureintro; exact Hskip (.inl Hdec)
    | some x =>
      obtain ⟨rep, sq, kd, key, val⟩ := x
      simp only [decodeRet, Hdec]
      wp_auto
      wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
      iNamed HR
      -- `_, done := r.applied[string(e.GetData())]`
      wp_apply wp_Entry_GetData.1 e DFrac.discard em $$ [$Hpbinit $He] as %ds1 ⟨#Hd1, -⟩
      wp_apply wp_bytes_to_string ds1 em.Data' DFrac.discard $$ [$Hd1] as -
      wp_apply wp_map_lookup2 go.string go.string mA A em.Data' (DFrac.own 1) $$ [$HA] as HA
      have Hdsome : (decodeOp em.Data').isSome := by rw [Hdec]; rfl
      rw [appliedOk_lookup A _ em.Data' HA Hdsome]
      try wp_auto
      wp_if_destruct
      · -- applied before: unlock, skip
        wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hwaiters Hrds]
        · inext
          unfold lockInv
          iexists ns, mW, W
          iframe
          ipureintro; exact HWdom
        iapply HΦ
        iapply Hkeep $$ HmK HK HmA HA
        ipureintro; exact Hskip (.inr (of_decide_eq_true Hif))
      have Hnew : em.Data' ∉ firstOcc ods := fun h => Hif (decide_eq_true h)
      -- the first occurrence of `em.Data'`: the operation applied, its answer recorded
      iclear Hkeep
      ihave Hfin : iprop(∀ Kn : GMap (List w8) (List w8),
          ⌜∀ k, (Kn !! k).getD [] = kvApply (kvFold (firstOcc ods)) em.Data' k⌝ -∗
          r.[RKV, go!"kv"] ↦ mK -∗ mK ↦$ Kn -∗
          r.[RKV, go!"applied"] ↦ mA -∗
          mA ↦$ A.insert em.Data' ((Kn !! key).getD (zero_val (List w8))) -∗
          runOwn γr r (ap ++ [em])) $$ []
      · iintro %Kn %HvalN HmK HK HmA HA'
        unfold runOwn
        have HvK : (Kn !! key).getD (zero_val (List w8)) =
            kvFold (firstOcc ods ++ [em.Data']) (dkey em.Data') := by
          rw [show zero_val (List w8) = [] from rfl, kvFold_snoc, HvalN,
            show dkey em.Data' = key by simp [dkey, Hdec]]
        iexists mK, Kn, mA, A.insert em.Data' ((Kn !! key).getD (zero_val (List w8))),
          ods ++ [some em.Data']
        rw [← Hraft, firstOcc_snoc, occStep_nmem _ em.Data' Hnew]
        iframe HmK HK HmA HA' Hce Hods'
        ipureintro
        refine ⟨fun k => ?_, ?_⟩
        · rw [kvFold_snoc]; exact HvalN k
        · rw [HvK]; exact appliedOk_insert A _ em.Data' HA Hnew Hdsome
      have HappE : kvApply (kvFold (firstOcc ods)) em.Data' =
          kvNext kd key val (kvFold (firstOcc ods)) := by simp [kvApply, Hdec]
      wp_if_destruct
      · -- a `Put`
        wp_apply wp_mapInsert go.string mK K key val $$ [$HK] as HK
        obtain ⟨Kn, HKn⟩ : ∃ Kn, Kn = <[key := val]> K := ⟨_, rfl⟩
        rw [← HKn]
        have HvalN : ∀ k, (Kn !! k).getD [] = kvApply (kvFold (firstOcc ods)) em.Data' k := by
          rw [HappE, HKn, kvNext, ite_eq_left (show W8 1 = opPutB from rfl)]
          exact kvMap_put K _ key val Hval
        apply_rest
      · have HnPut := Hif
        wp_if_destruct
        · -- an `Append`
          wp_apply wp_map_lookup1 go.string go.string mK K key (DFrac.own 1) $$ [$HK] as HK
          wp_apply wp_mapInsert go.string mK K key ((K !! key).getD (zero_val (List w8)) ++ val)
            $$ [$HK] as HK
          obtain ⟨Kn, HKn⟩ : ∃ Kn, Kn = <[key := (K !! key).getD (zero_val (List w8)) ++ val]> K :=
            ⟨_, rfl⟩
          rw [← HKn]
          have HvalN : ∀ k, (Kn !! k).getD [] = kvApply (kvFold (firstOcc ods)) em.Data' k := by
            rw [HappE, HKn, kvNext, ite_eq_right (show ¬ W8 4 = opPutB by decide),
              ite_eq_left (show W8 4 = opAppendB from rfl)]
            exact kvMap_append K _ key val Hval
          apply_rest
        · obtain ⟨Kn, HKn⟩ : ∃ Kn, Kn = K := ⟨_, rfl⟩
          rw [← HKn]
          have HvalN : ∀ k, (Kn !! k).getD [] = kvApply (kvFold (firstOcc ods)) em.Data' k := by
            rw [HappE, HKn, kvNext, ite_eq_right (show ¬ kd = opPutB from HnPut),
              ite_eq_right (show ¬ kd = opAppendB from Hif)]
            exact Hval
          apply_rest


end proof

end kv
end EtcdGrove
end Perennial
