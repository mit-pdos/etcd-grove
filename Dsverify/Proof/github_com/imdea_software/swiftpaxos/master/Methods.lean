/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/master/Methods.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`m.GetReplicaList(args, reply)` and `m.GetLeader(args, reply)` (internal specs and proofs).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [master.Assumptions]

/-- `m.GetReplicaList(args, reply)`: blocks until `run` has finished its initialization (the
membership is then fixed), and answers it, `Ready`, with one alive flag per replica. -/
abbrev master.Master.GetReplicaList.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (args reply : Loc)
    (rv : replica.defs.GetReplicaListReply),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.isMaster m γc γm N ∗ reply ↦ rv }}
    (App (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"GetReplicaList"))
      (Val #args)) (Val #reply))
  {{ RET #(interface.nil : GoInterface);
      ∃ (s1 s2 : GoSlice) (nodes : List GoString) (alive : List Bool),
        reply ↦ replica.defs.GetReplicaListReply.mk s1 s2 true ∗ s1 ↦* nodes ∗ s2 ↦* alive ∗
        (∃ fr, sp.cfg γc γm nodes.length fr nodes) ∗ ⌜alive.length = nodes.length⌝ }}

/-- `m.GetLeader(args, reply)`: some id (or `reply` unchanged), no error. -/
abbrev master.Master.GetLeader.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (args reply : Loc) (rv : replica.defs.GetLeaderReply),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.isMaster m γc γm N ∗ reply ↦ rv }}
    (App (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"GetLeader"))
      (Val #args)) (Val #reply))
  {{ RET #(interface.nil : GoInterface); ∃ id : w64, reply ↦ replica.defs.GetLeaderReply.mk id }}

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [master.Assumptions] [dlog.Assumptions]

set_option maxHeartbeats 4000000 in
theorem master.Master.GetReplicaList.wp_proof
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG)) :
    master.Master.GetReplicaList.spec := fun m γc γm N args reply rv => by
  wp_start as ⟨#Hm, Hreply⟩
  unfold master.isMaster
  iNamed Hm
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  ipersist master
  ipersist reply
  wp_for
  iNamed HR
  wp_auto
  wp_if_destruct
  · -- not initialized: wait
    ihave #Hlk := sync.Mutex_is_Locker lk (master.lockInv m γm N leaderS aliveS latS) $$ [] Hmu
    · iPkgInit
    wp_apply sync.Cond.wp_Wait cd (interface.mk (go.GoType.PointerType sync.Mutex.ty) #lk)
        iprop(sync.ownMutex lk ∗ master.lockInv m γm N leaderS aliveS latS)
        $$ [$HisCond $Hlk Hlocked Hlists Hleaders Halives Hlats Hfi]
      as ⟨Hlocked, HR⟩
    · iframe Hlocked
      unfold master.lockInv
      iexists nl, al, pl, nodes, addrs, ports, leaders, alive, lats, fi
      iframe
      ipureintro; exact Hwf
    wp_for_post
    iframe
  -- initialized
  have hfi : fi = true := by cases fi <;> simp_all
  subst hfi
  simp only [Bool.not_true, ↓reduceIte, _root_.decide_true]
  have hfull : nodes.length = N := Hwf.2.2.2.2 rfl
  ihave Hl := Hlists
  unfold master.lists
  rw [if_pos hfull]
  icases Hl with ⟨#HnlF, #HalF, #HplF, #Hnl, #Hal, #Hpl, #Hmem⟩
  ihave %Hnllen := ownSlice_len _ _ _ $$ Hnl
  ihave %Halen := ownSlice_len _ _ _ $$ Halives
  have hN : N ≤ 5 := HN.2
  have hlen : nl.len = W64 N := by word
  wp_auto
  rw [decide_eq_true hlen]
  wp_auto
  wp_apply wp_slice_make2 (V := GoString) as %s1 ⟨Hs1, Hc1⟩
  · ipureintro; word
  wp_apply wp_slice_make2 (V := Bool) as %s2 ⟨Hs2, Hc2⟩
  · ipureintro; word
  rename_i key_ptr
  irename : (key_ptr ↦ Perennial.zero_val w64 : IProp netDistGF) => ikey
  ihave HI : (∃ (j kv : w64) (nv : GoString) (s1 s2 : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "ikey" ∷ key_ptr ↦ kv ∗ "node" ∷ node_ptr ↦ nv ∗
      "Hreply" ∷ reply ↦ replica.defs.GetReplicaListReply.mk s1 s2 true ∗
      "Hs1" ∷ s1 ↦* nodes.take (sint.nat j) ∗ "Hc1" ∷ ownSliceCap GoString s1 (DFrac.own 1) ∗
      "Hs2" ∷ s2 ↦* alive.take (sint.nat j) ∗ "Hc2" ∷ ownSliceCap Bool s2 (DFrac.own 1) ∗
      "Halives" ∷ aliveS ↦* alive ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nl.len⌝ : IProp netDistGF)
    $$ [i ikey node Hreply Hs1 Hc1 Hs2 Hc2 Halives]
  · iexists _, _, _, s1, s2
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.take_zero]
    simp only [List.replicate_zero]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have hj : sint.nat j < nodes.length := by word
    list_elem nodes (sint.nat j) as nd
    list_elem alive (sint.nat j) as al1
    rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z nl.len from ⟨Hj.1, Hif⟩)]
    wp_apply wp_load_slice_index _ (sint.Z j) _ _ nd Hj.1 $$ [Hnl] as -
    · iframe Hnl; ipureintro; exact Hnd_lookup
    wp_apply wp_slice_literal (V := GoString) [nd]
    isplitr
    · ipureintro; rfl
    iintro %ls ⟨Hls, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hs1 $Hc1 $Hls] as %s1' ⟨Hs1, Hc1, -⟩
    have hja : sint.Z j < sint.Z aliveS.len := by have := Hwf.2.2.1; word
    rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z aliveS.len from ⟨Hj.1, hja⟩)]
    wp_apply wp_load_slice_index _ (sint.Z j) _ _ al1 Hj.1 $$ [Halives] as Halives
    · iframe; ipureintro; exact Hal1_lookup
    wp_apply wp_slice_literal (V := Bool) [al1]
    isplitr
    · ipureintro; rfl
    iintro %lb ⟨Hlb, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hs2 $Hc2 $Hlb] as %s2' ⟨Hs2, Hc2, -⟩
    wp_for_post
    iframe
    iexists _, _, _, s1', s2'
    rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, List.take_add_one,
      Hnd_lookup, Hal1_lookup]
    simp only [Option.toList_some]
    iframe
    ipureintro; word
  · have hjN : sint.nat j = N := by word
    rw [hjN, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk (go.GoType.SliceType go.string) #s1]
    isplitr
    · ipureintro; rfl
    iintro %ps ⟨-, -⟩
    wp_auto
    wp_apply master.wp_Printf wp_Printf $$ [$Hlg $Hquiet]
    ihave Hlists := master.lists_full m γm N nl al pl nodes addrs ports hfull $$ HnlF HalF HplF
      Hnl Hal Hpl Hmem
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hleaders Halives Hlats Hfi]
    · inext
      unfold master.lockInv
      iexists nl, al, pl, nodes, addrs, ports, leaders, alive, lats, true
      iframe
      isplitl [Hlists]
      · iexact Hlists
      ipureintro; exact Hwf
    ihave #Hcfg := sp.cfg_intro (γc := γc) (γm := γm) c nodes $$ [$Hconf $Hmem]
    · ipureintro; exact ⟨by rw [hfull, HN.1], by rw [HN.1]; exact master.regOk_nodeOf Hwf.1⟩
    iapply HΦ
    iexists s1, s2, nodes, alive
    iframe
    isplitr
    · iexists _; rw [hfull, ← HN.1]; iexact Hcfg
    ipureintro; have := Hwf.2.2.1; omega

set_option maxHeartbeats 4000000 in
theorem master.Master.GetLeader.wp_proof :
    master.Master.GetLeader.spec := fun m γc γm N args reply rv => by
  wp_start as ⟨#Hm, Hreply⟩
  unfold master.isMaster
  iNamed Hm
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  unfold master.lockInv
  iNamed HR
  rename_i key_ptr
  irename : (key_ptr ↦ Perennial.zero_val w64 : IProp netDistGF) => ikey
  ihave %Hldl := ownSlice_len _ _ _ $$ Hleaders
  ipersist reply
  wp_join iprop(∃ gv : replica.defs.GetLeaderReply, reply ↦ gv ∗ leaderS ↦* leaders)
    at next with [Hreply Hleaders i ikey l] as ⟨%gv, Hreply, Hleaders⟩
  · ihave HI : (∃ (j kv : w64) (lv : Bool) (gv : replica.defs.GetLeaderReply),
        "i" ∷ i_ptr ↦ j ∗ "ikey" ∷ key_ptr ↦ kv ∗ "l" ∷ l_ptr ↦ lv ∗ "Hreply" ∷ reply ↦ gv ∗
        "Hleaders" ∷ leaderS ↦* leaders ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z leaderS.len⌝ : IProp netDistGF)
      $$ [i ikey l Hreply Hleaders]
    · iexists _, _, _, _
      iframe
      ipureintro; word
    wp_for HI
    wp_if_destruct
    · list_elem leaders (sint.Z j).toNat as b
      rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z leaderS.len from ⟨Hj.1, Hif⟩)]
      wp_apply wp_load_slice_index _ (sint.Z j) _ _ b Hj.1 $$ [Hleaders] as Hleaders
      · iframe; ipureintro; exact Hb_lookup
      cases b
      · wp_auto
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro; word
      · wp_auto
        wp_for_post
        iframe
        ipureintro; rfl
    · iframe
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hleaders Halives Hlats Hfi]
  · inext
    iexists nl, al, pl, nodes, addrs, ports, leaders, alive, lats, fi
    iframe
    ipureintro
    exact Hwf
  iapply HΦ
  iexists gv.LeaderId'
  iexact Hreply

end proof

end Perennial.github_com.imdea_software.swiftpaxos
