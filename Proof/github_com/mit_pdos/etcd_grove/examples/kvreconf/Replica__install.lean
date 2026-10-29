/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__install.lean`. Lean-first
(no Rocq counterpart).

The metadata's `ConfState` cloned (read-only from then on; `nil` clones to `nil`, the zero record,
which the premise makes `mL`'s); under the lock the fields replaced (the shared ones with both
halves), then the loop over the waiters (`wp_map_for_range_mut`) answers each operation the
snapshot's table records with its answer (`AppliedOk`'s `AnsOk`: `waitP` at `L`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__install
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetConfState
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetLearners
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetLearnersNext
public import Spec.google_golang_org.protobuf.proto.CloneConfState
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Halves
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [StorageModel GF] [AllG GF]

set_option hygiene false in
/-- `install` once the clone `csn` of the metadata's `ConfState` is in hand (`HcsN`). -/
local macro "install_rest" : tactic => `(tactic| (
    try wp_auto
    wp_apply sync.Mutex.wp_Lock _ _ $$ [$(frameH `Hmu)] as ⟨Hlocked, HR⟩
    iNamed HR
    iunfold repShared at Hrep
    icases Hrep with ⟨%mA0, %A0, %csp0, %c0, %idx0, %ap0, HmA', HA', Hcs', Hidx', #HcsO0, #Hap0, %HA0⟩
    icombine HmA HmA' gives %HmAeq
    subst HmAeq
    icombine Hcs Hcs' gives %Hcseq
    subst Hcseq
    icombine Hidx Hidx' gives %Hieq
    subst Hieq
    ihave HmAf := (typedPointsto_half_split _ mA (1 : Qp)).2 $$ [$(frameH `HmA) $(frameH `HmA')]
    ihave Hcsf := (typedPointsto_half_split _ csp (1 : Qp)).2 $$ [$(frameH `Hcs) $(frameH `Hcs')]
    ihave Hidxf := (typedPointsto_half_split _ idx (1 : Qp)).2 $$ [$(frameH `Hidx) $(frameH `Hidx')]
    try wp_auto
    wp_apply wp_GetIndex mdp dq md $$ [$(frameH `Hpb) $(frameH `Hsm)] as Hsm
    try wp_auto
    icases (typedPointsto_half_split _ mA' (1 : Qp)).1 $$ HmAf with ⟨HmA, HmA'⟩
    icases (typedPointsto_half_split _ csn (1 : Qp)).1 $$ Hcsf with ⟨Hcs, Hcs'⟩
    icases (typedPointsto_half_split _ md.Index' (1 : Qp)).1 $$ Hidxf with ⟨Hidx, Hidx'⟩
    -- the waiters the snapshot covers
    try wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range_mut (fun (_ : Nat) (m' : GMap (List w8) Loc) =>
        iprop(∃ (o0 : List w8) (c1 : Loc),
        "o" ∷ o_ptr ↦ o0 ∗ "ch" ∷ ch_ptr ↦ c1 ∗ "applied" ∷ applied_ptr ↦ mA' ∗ "HAf" ∷ mA' ↦$ A' ∗
        "HmW" ∷ r.[RReplica, go!"waiters"] ↦ mW ∗ "r" ∷ r_ptr ↦ r ∗
        "Hws" ∷ [∗map] d ↦ ch ∈ m', waiterOk γr d ch))
      _ _ _ mW W $$ HW
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [o ch applied HAf HmW r Hwaiters]
    · iexists _, _
      simp only [named]
      iframe
    isplitr
    · imodintro
      iintro %i %key %v %m' ⟨%Hki, %Hmv, %Hagree⟩ HP Hm
      iNamed HP
      have hm'v : m' !! key = some v := by rw [Hagree i key (Nat.le_refl _) Hki]; exact Hmv
      try wp_auto
      wp_apply wp_map_lookup2 go.string go.string mA' A' key (DFrac.own 1) $$ [$(frameH `HAf)] as HAf
      cases HAk : A' !! key with
      | none =>
        simp only [Option.getD_none, Option.isSome_none, decide_false, Bool.false_eq_true]
        try wp_auto
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists m'
        iframe Hm
        isplitl
        · iexists key, v
          simp only [named]
          iframe
        ipureintro
        intro k _; rfl
      | some w =>
        simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
        try wp_auto
        icases (BigSepM.bigSepM_delete (Φ := fun d ch => waiterOk (GF := GF) γr d ch) hm'v).1
          $$ Hws with ⟨Hwt, Hws⟩
        try wp_auto
        wp_apply wp_mapDelete $$ [$(frameH `Hm)] as Hm
        iunfold waiterOk at Hwt
        icases Hwt with ⟨%γh, #Hho, Hprod⟩
        ihave #Hw : waitP γr key w $$ []
        · unfold waitP
          iexists L
          iframe HL
          ipureintro; exact HA'.2 _ _ HAk
        try wp_auto
        wp_apply wp_handoff_send (t := go.string) γh v (waitP γr key) iprop(True) iprop(False)
          w $$ [$(frameH `Hho) $(frameH `Hprod) $(frameH `Hw)]
        iintro -
        try wp_auto
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Hm
        isplitl
        · iexists key, v
          simp only [named]
          iframe
        ipureintro
        intro k hk
        rw [GMap.lookup_delete_ne _ (Ne.symm hk)]
    iintro %W' HP HW
    iNamed HP
    icases ownMap_halves_split mA' A' $$ [$(frameH `HAf)] with ⟨HA1, HA2⟩
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$(frameH `Hmu) $(frameH `Hlocked) HmA' HA2 Hcs' Hidx'
        HmW HW Hws Hns Hseq HmR HRd Hreads]
    · inext
      unfold lockInv repShared
      iexists ns, mW, W', mR, Rd
      iframe
      isplitl [HmA' HA2 Hcs' Hidx']
      · iexists mA', A', csn, md.ConfState', md.Index', L
        iframe HmA' HA2 Hcs' Hidx' HcsN HL
        ipureintro; exact HA'
      · ipureintro; exact HRdom
    -- the statistics
    try wp_auto
    ihave #Hc1 := isStats_field sts go!"SnapshotsInstalled" (by decide) $$ Hstats
    ihave #Hc2 := isStats_field sts go!"SnapshotsInstalledJoint" (by decide) $$ Hstats
    ihave #Hc3 := isStats_field sts go!"SnapshotsInstalledLearners" (by decide) $$ Hstats
    wp_apply wp_add sts _ $$ [$(frameH `Hpkg) $(frameH `Hc1)]
    try wp_auto
    wp_apply wp_GetVotersOutgoing csn DFrac.discard md.ConfState' $$ [$(frameH `Hpb) $(frameH `HcsN)]
      as %s1 ⟨Hs1, -⟩
    ihave %Hs1l := ownSlice_len $$ Hs1
    try wp_auto
    ihave Hfin : iprop(smOpt mdp dq md ∗ ∃ csp' : Loc, repOwn γr r L md.Index' csp' mL mA' A')
        $$ [Hsm HmK HKf HmA HA1 Hcs Hidx]
    · iframe Hsm
      iexists csn
      unfold repOwn
      iexists mK', K', md.ConfState'
      iframe HmK HKf HmA HA1 Hcs Hidx HcsN HL HmL
      ipureintro; exact ⟨HLlen', HK', HA', HmLc⟩
    try wp_if_destruct
    all_goals
      try wp_apply wp_add sts _ $$ [$(frameH `Hpkg) $(frameH `Hc2)]
      try wp_auto
      wp_apply wp_GetLearners csn DFrac.discard md.ConfState' $$ [$(frameH `Hpb) $(frameH `HcsN)]
        as %s2 ⟨Hs2, -⟩
      ihave %Hs2l := ownSlice_len $$ Hs2
      try wp_auto
      try wp_if_destruct
      all_goals
        try wp_apply wp_GetLearnersNext csn DFrac.discard md.ConfState' $$ [$(frameH `Hpb) $(frameH `HcsN)] as %s3 ⟨Hs3, -⟩
        try wp_auto
        try wp_if_destruct
        all_goals
          try wp_apply wp_add sts _ $$ [$(frameH `Hpkg) $(frameH `Hc3)]
          try wp_auto
          iapply HΦ
          iexact Hfin
  ))

theorem Replica.install.wp_proof
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_GetConfState : raftpb.SnapshotMetadata.GetConfState.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetVotersOutgoing : raftpb.ConfState.GetVotersOutgoing.spec (GF := GF) (hG := hG))
    (wp_GetLearners : raftpb.ConfState.GetLearners.spec (GF := GF) (hG := hG))
    (wp_GetLearnersNext : raftpb.ConfState.GetLearnersNext.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.CloneConfState.spec (GF := GF) (hG := hG)) :
    Replica.install.spec (GF := GF) (hG := hG) := by
  intro γr vs id r n st sts ap idx csp m mA A mdp dq md mK' mA' K' A' L mL HLlen HLlen' HK' HA' HmLc
  wp_start as ⟨#Hrep, Hown, Hsm, HKf, HAf, #HL, #HmL⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  iunfold repOwn at Hown
  iNamed Hown
  have HLlen2 : ((L.length : Int) < 2 ^ 61) := HLlen'
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_GetConfState mdp dq md $$ [$Hpb $Hsm] as %pc ⟨Hpc, Hback⟩
  iunfold csOptA at Hpc
  icases Hpc with (%Hnil | Hpc | #Hpc)
  · obtain ⟨Hp, Hc⟩ := Hnil
    subst Hp
    ihave Hsm := Hback $$ []
    · unfold csOptA; ileft; ipureintro; exact ⟨rfl, Hc⟩
    try wp_auto
    wp_apply wp_Clone.2 $$ [$Hproto]
    obtain ⟨csn, Hcsn⟩ : ∃ csn : Loc, csn = null := ⟨_, rfl⟩
    rw [← Hcsn]
    ihave #HcsN : csOpt csn DFrac.discard md.ConfState' $$ []
    · unfold csOpt; ileft; ipureintro; exact ⟨Hcsn, Hc⟩
    install_rest
  · try wp_auto
    wp_apply wp_Clone.1 pc dq md.ConfState' $$ [$Hproto $Hpc] as %csn ⟨Hpc, Hcl⟩
    ihave Hsm := Hback $$ [Hpc]
    · unfold csOptA; iright; ileft; iexact Hpc
    imod csPts_persist csn (DFrac.own 1) md.ConfState' false $$ Hcl with #Hcl
    ihave #HcsN : csOpt csn DFrac.discard md.ConfState' $$ []
    · unfold csOpt; iright; iexact Hcl
    install_rest
  · try wp_auto
    ihave #Hpc' := csPts_weaken pc DFrac.discard md.ConfState' true $$ Hpc
    wp_apply wp_Clone.1 pc DFrac.discard md.ConfState' $$ [$Hproto $Hpc'] as %csn ⟨-, Hcl⟩
    ihave Hsm := Hback $$ []
    · unfold csOptA; iright; iright; iexact Hpc
    imod csPts_persist csn (DFrac.own 1) md.ConfState' false $$ Hcl with #Hcl
    ihave #HcsN : csOpt csn DFrac.discard md.ConfState' $$ []
    · unfold csOpt; iright; iexact Hcl
    install_rest

end proof

end kvreconf
end EtcdGrove
end Perennial
