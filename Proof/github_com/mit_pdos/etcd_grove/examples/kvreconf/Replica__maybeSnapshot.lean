/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__maybeSnapshot.lean`.
Lean-first (no Rocq counterpart).

Under the lock the applier reads its own halves (`r.index = len ap`, `r.cs = csp`) and encodes its
maps (`encodeState`: `ap`'s state, `kvr_snapOk_of`). With a configuration and an index past the stored
snapshot's, `CreateSnapshot` takes the frozen entry at `len ap` (`frozenTo_at`: `ap`'s last term),
the snapshot certified in the registry (`kvr_snap_make`) and the delivered log (`storDL`); its
`ErrSnapOutOfDate` answer is refuted by `snapIndex < len ap`, so the `panic` is unreachable.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__maybeSnapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.encodeState
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorageApi
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunFrozen
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.SnapMake
public import Proof.go_etcd_io.raft.v3.Base
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
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

set_option hygiene false in
/-- No snapshot taken: the lock released, `data` still `nil`, `snapIndex` returned. -/
local macro "ms_nil" : tactic => `(tactic| (
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$(frameH `Hmu) $(frameH `Hlocked) HR]
    · inext; iexact HR
    try wp_auto
    iapply HΦ
    iexists sv0
    iframe Hsx
    isplitl [HmK HK HmA HA Hcs Hidx Hown]
    · iapply Hown; iframe
    ipureintro; exact ⟨Hsi, .inl rfl⟩
  ))

theorem Replica.maybeSnapshot.wp_proof
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_encodeState : encodeState.spec (GF := GF) (hG := hG))
    (wp_GetVotersOutgoing : raftpb.ConfState.GetVotersOutgoing.spec (GF := GF) (hG := hG))
    (wp_CreateSnapshot : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG)) :
    Replica.maybeSnapshot.spec (GF := GF) (hG := hG) := by
  intro γr vs id r n st sts ρ ap csp m mA A D cp sv0 snapIndex Hpre Hcp Hsi
  wp_start as ⟨#Hrr, Hown, Hsx, #Hfz, #Hdl⟩
  ihave #Hrr' := Hrr
  iunfold isReplicaR at Hrr'
  iNamed Hrr'
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  iunfold repOwn at Hown
  iNamed Hown
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  have Hlen' : uint.Z (W64 (ap.length : Int)) = (ap.length : Int) := by word
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  try wp_auto
  ihave Hown : iprop(r.[RReplica, go!"kv"] ↦ mK ∗ mK ↦$ K ∗
      r.[RReplica, go!"applied"] ↦{DFrac.own (1 : Qp).half} mA ∗
      mA ↦${DFrac.own (1 : Qp).half} A ∗
      r.[RReplica, go!"cs"] ↦{DFrac.own (1 : Qp).half} csp ∗
      r.[RReplica, go!"index"] ↦{DFrac.own (1 : Qp).half} W64 ap.length -∗
      repOwn γr r ap (W64 ap.length) csp m mA A) $$ []
  · iintro ⟨HmK, HK, HmA, HA, Hcs, Hidx⟩
    unfold repOwn; iexists mK, K, c; iframe; iframe Hap HcsO Hcfg
    ipureintro; exact ⟨Hlen, Hval, HA, Hcsm, Hsz⟩
  wp_if_destruct
  all_goals try wp_auto
  all_goals try wp_if_destruct
  · ms_nil
  · wp_apply wp_encodeState mK mA K A (DFrac.own 1) (DFrac.own (1 : Qp).half) $$ [$Hpkg $HK $HA]
      as %sl ⟨HK, HA, %kvs, %ops, Hsl, %Hkv⟩
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HR]
    · inext; iexact HR
    try wp_auto
    wp_if_destruct
    · iapply HΦ
      iexists sv0
      iframe Hsx
      isplitl [HmK HK HmA HA Hcs Hidx Hown]
      · iapply Hown; iframe
      ipureintro; exact ⟨Hsi, .inl rfl⟩
    -- the snapshot: its entry, its certificate, its delivered log
    have Hlt : uint.nat snapIndex < ap.length := by word
    have HapD : ap.length ≤ D.length := Hpre.length_le
    have Hne : ap ≠ [] := by intro h; subst h; simp at Hlt
    have Hlast : D[ap.length - 1]? = ap.getLast? := by
      rw [List.getLast?_eq_getElem?]
      obtain ⟨t, rfl⟩ := Hpre
      rw [List.getElem?_append_left (by have := List.length_pos_iff.mpr Hne; omega)]
    icases frozenTo_at ρ.γs cp D ap.length (by omega) HapD $$ Hfz with ⟨%e, #He, %Hee⟩
    obtain ⟨x, Hx⟩ : ∃ x, ap.getLast? = some x := Option.isSome_iff_exists.mp (by
      simp [List.getLast?_eq_getLast Hne])
    have Hex := Hee x (by rw [Hlast, Hx])
    have Hterm : Option.map LogEntry.term ap.getLast? = some e.Term' := by
      rw [Hx, Hex]; rfl
    have Hdat := kvr_snapOk_of ap K A kvs ops Hkv.1 Hkv.2 Hval HA
    iunfold csOpt at HcsO
    icases HcsO with (%Hnull | #HcsM)
    · exact absurd Hnull.1 (by assumption)
    imod kvr_snap_make γr vs ap (W64 ap.length) e.Term' (encState kvs ops) m c sv0 (by word) (by word)
        (by word) Hterm Hcsm Hsz Hdat $$ Hcl Hap Hcfg with #Hsv
    ihave #Hinit := isInitialized_access $$ Hraft
    iunfold isInitialized at Hinit
    iNamed Hinit
    icases ErrSnapOOD with ⟨%eood, #Heood⟩
    wp_apply Storage.wp_CreateSnapshot wp_CreateSnapshot st ρ.ms ρ.γs (kvrJ γr.cluster id)
        (W64 ap.length) e csp DFrac.discard (some c) sl (encState kvs ops) sv0 eood
        $$ [$HstRec $Hraft $HmsInv $Hsx $Hsl $Heood]
      as %snap %err ⟨-, Hres⟩
    · rw [show uint.nat (W64 (ap.length : Int)) = ap.length by word]
      iframe He
      isplitl []
      · unfold kvrJ; iexact Hsv
      isplitl []
      · unfold kvrJ storDL; iexists n, kvrRaftN, D; iframe HisNode Hdl; ipureintro; exact HapD
      unfold memCsArg; iexact HcsM
    icases Hres with (⟨%Herr, Hsx, -⟩ | ⟨%Hbad, -, -⟩)
    rotate_left
    · exfalso; rw [Hsi] at Hbad; have := Hbad.2.2; word
    subst Herr
    try wp_auto
    ihave #Hc1 := isStats_field sts go!"SnapshotsTaken" (by decide) $$ Hstats
    ihave #Hc2 := isStats_field sts go!"SnapshotsTakenJoint" (by decide) $$ Hstats
    wp_apply wp_add sts _ $$ [$Hpkg $Hc1]
    try wp_auto
    ihave #HcsO : csOpt csp DFrac.discard c $$ []
    · unfold csOpt; iright; iexact HcsM
    wp_apply wp_GetVotersOutgoing csp DFrac.discard c $$ [$Hpb $HcsO] as %vo ⟨-, -⟩
    try wp_auto
    try wp_if_destruct
    all_goals
      try wp_apply wp_add sts _ $$ [$Hpkg $Hc2]
      try wp_auto
      iapply HΦ
      iexists _
      iframe Hsx
      isplitl [HmK HK HmA HA Hcs Hidx Hown]
      · iapply Hown; iframe
      ipureintro; exact ⟨rfl, .inr ⟨rfl, Hlt⟩⟩
  · ms_nil

end proof

end kvreconf
end EtcdGrove
end Perennial
