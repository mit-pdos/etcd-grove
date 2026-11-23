/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/DecStruct.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The codec's decoders of the rpc argument and reply structs (`rpcDec_defs_*`) meet their parsers.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.DecSync

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]

open sp

def ownRA (v : replica.defs.RegisterArgs) (x : KitVal) : IProp GF :=
  iprop(⌜x = .registerArgs v.Addr' v.Port'⌝)
def ownRR (v : replica.defs.RegisterReply) : KitVal → IProp GF
  | .registerReply i ns rd il => iprop(⌜v.ReplicaId' = i ∧ v.Ready' = rd ∧ v.IsLeader' = il⌝ ∗
      v.NodeList' ↦* ns)
  | _ => iprop(False)
def ownGLR (v : replica.defs.GetLeaderReply) (x : KitVal) : IProp GF :=
  iprop(⌜x = .getLeaderReply v.LeaderId'⌝)
def ownGRLR (v : replica.defs.GetReplicaListReply) : KitVal → IProp GF
  | .getReplicaListReply rs al rd => iprop(⌜v.Ready' = rd⌝ ∗ v.ReplicaList' ↦* rs ∗
      v.AliveList' ↦* al)
  | _ => iprop(False)
def ownPA (v : replica.defs.PingArgs) (x : KitVal) : IProp GF :=
  iprop(⌜x = .pingArgs v.ActAsLeader'⌝)
def ownBTLR (v : replica.defs.BeTheLeaderReply) (x : KitVal) : IProp GF :=
  iprop(⌜x = .beTheLeaderReply v.Leader' v.NextLeader'⌝)
/-- A field-less struct holds `c`. -/
def ownEmpty {T : Type} (c : KitVal) (_v : T) (x : KitVal) : IProp GF := iprop(⌜x = c⌝)

theorem wp_rpcDec_defs_RegisterArgs (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_defs_RegisterArgs)) (Val #b))
    {{ (v : replica.defs.RegisterArgs) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost pRegisterArgs ownRA b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_string $$ Hb as %v0 %r0 %ok0 Hpost
  unfold decPost
  icases Hpost with (⟨%H0, Hb⟩ | ⟨%a0, %rest0, %H0, %Hown0, Hrest⟩)
  · obtain ⟨H0, rfl⟩ := H0
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pRegisterArgs, H0], rfl⟩
  obtain ⟨H0, rfl⟩ := H0
  subst Hown0
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_apply wp_rpcDec_int $$ Hr as %v1 %r1 %ok1 Hpost
  unfold decPost
  icases Hpost with (⟨%H1, Hr⟩ | ⟨%a1, %rest1, %H1, %Hown1, Hrest⟩)
  · obtain ⟨H1, rfl⟩ := H1
    ihave Hb := Hback $$ Hr
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pRegisterArgs, H0, H1], rfl⟩
  obtain ⟨H1, rfl⟩ := H1
  subst Hown1
  ihave Hrest := restOf_comp $$ Hback Hrest
  wp_auto
  iapply HΦ; iright; iexists .registerArgs v0 v1, rest1
  iframe Hrest
  isplitr
  · ipureintro; exact ⟨by simp [pRegisterArgs, H0, H1], rfl⟩
  unfold ownRA
  ipureintro; rfl

theorem wp_rpcDec_defs_RegisterReply (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_defs_RegisterReply)) (Val #b))
    {{ (v : replica.defs.RegisterReply) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost pRegisterReply ownRR b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_int $$ Hb as %v0 %r0 %ok0 Hpost
  unfold decPost
  icases Hpost with (⟨%H0, Hb⟩ | ⟨%a0, %rest0, %H0, %Hown0, Hrest⟩)
  · obtain ⟨H0, rfl⟩ := H0
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pRegisterReply, H0], rfl⟩
  obtain ⟨H0, rfl⟩ := H0
  subst Hown0
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_apply wp_rpcDec_S_string $$ Hr as %v1 %r1 %ok1 Hpost
  unfold decPost
  icases Hpost with (⟨%H1, Hr⟩ | ⟨%a1, %rest1, %H1, Hown1, Hrest⟩)
  · obtain ⟨H1, rfl⟩ := H1
    ihave Hb := Hback $$ Hr
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pRegisterReply, H0, H1], rfl⟩
  obtain ⟨H1, rfl⟩ := H1
  ihave Hrest := restOf_comp $$ Hback Hrest
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_apply wp_rpcDec_bool $$ Hr as %v2 %r2 %ok2 Hpost
  unfold decPost
  icases Hpost with (⟨%H2, Hr⟩ | ⟨%a2, %rest2, %H2, %Hown2, Hrest⟩)
  · obtain ⟨H2, rfl⟩ := H2
    ihave Hb := Hback $$ Hr
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pRegisterReply, H0, H1, H2], rfl⟩
  obtain ⟨H2, rfl⟩ := H2
  subst Hown2
  ihave Hrest := restOf_comp $$ Hback Hrest
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_apply wp_rpcDec_bool $$ Hr as %v3 %r3 %ok3 Hpost
  unfold decPost
  icases Hpost with (⟨%H3, Hr⟩ | ⟨%a3, %rest3, %H3, %Hown3, Hrest⟩)
  · obtain ⟨H3, rfl⟩ := H3
    ihave Hb := Hback $$ Hr
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pRegisterReply, H0, H1, H2, H3], rfl⟩
  obtain ⟨H3, rfl⟩ := H3
  subst Hown3
  ihave Hrest := restOf_comp $$ Hback Hrest
  wp_auto
  iapply HΦ; iright; iexists .registerReply v0 a1 v2 v3, rest3
  iframe Hrest
  isplitr
  · ipureintro; exact ⟨by simp [pRegisterReply, H0, H1, H2, H3], rfl⟩
  unfold ownRR
  dsimp only
  unfold ownSliceOf
  iframe
  ipureintro; exact ⟨rfl, rfl, rfl⟩

theorem wp_rpcDec_defs_GetLeaderReply (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_defs_GetLeaderReply)) (Val #b))
    {{ (v : replica.defs.GetLeaderReply) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost pGetLeaderReply ownGLR b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_int $$ Hb as %v0 %r0 %ok0 Hpost
  unfold decPost
  icases Hpost with (⟨%H0, Hb⟩ | ⟨%a0, %rest0, %H0, %Hown0, Hrest⟩)
  · obtain ⟨H0, rfl⟩ := H0
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pGetLeaderReply, H0], rfl⟩
  obtain ⟨H0, rfl⟩ := H0
  subst Hown0
  wp_auto
  iapply HΦ; iright; iexists .getLeaderReply v0, rest0
  iframe Hrest
  isplitr
  · ipureintro; exact ⟨by simp [pGetLeaderReply, H0], rfl⟩
  unfold ownGLR
  ipureintro; rfl

theorem wp_rpcDec_defs_GetReplicaListReply (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_defs_GetReplicaListReply)) (Val #b))
    {{ (v : replica.defs.GetReplicaListReply) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost pGetReplicaListReply ownGRLR b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_S_string $$ Hb as %v0 %r0 %ok0 Hpost
  unfold decPost
  icases Hpost with (⟨%H0, Hb⟩ | ⟨%a0, %rest0, %H0, Hown0, Hrest⟩)
  · obtain ⟨H0, rfl⟩ := H0
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pGetReplicaListReply, H0], rfl⟩
  obtain ⟨H0, rfl⟩ := H0
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_apply wp_rpcDec_S_bool $$ Hr as %v1 %r1 %ok1 Hpost
  unfold decPost
  icases Hpost with (⟨%H1, Hr⟩ | ⟨%a1, %rest1, %H1, Hown1, Hrest⟩)
  · obtain ⟨H1, rfl⟩ := H1
    ihave Hb := Hback $$ Hr
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pGetReplicaListReply, H0, H1], rfl⟩
  obtain ⟨H1, rfl⟩ := H1
  ihave Hrest := restOf_comp $$ Hback Hrest
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_apply wp_rpcDec_bool $$ Hr as %v2 %r2 %ok2 Hpost
  unfold decPost
  icases Hpost with (⟨%H2, Hr⟩ | ⟨%a2, %rest2, %H2, %Hown2, Hrest⟩)
  · obtain ⟨H2, rfl⟩ := H2
    ihave Hb := Hback $$ Hr
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pGetReplicaListReply, H0, H1, H2], rfl⟩
  obtain ⟨H2, rfl⟩ := H2
  subst Hown2
  ihave Hrest := restOf_comp $$ Hback Hrest
  wp_auto
  iapply HΦ; iright; iexists .getReplicaListReply a0 a1 v2, rest2
  iframe Hrest
  isplitr
  · ipureintro; exact ⟨by simp [pGetReplicaListReply, H0, H1, H2], rfl⟩
  unfold ownGRLR
  dsimp only
  unfold ownSliceOf
  iframe
  ipureintro; rfl

theorem wp_rpcDec_defs_PingArgs (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_defs_PingArgs)) (Val #b))
    {{ (v : replica.defs.PingArgs) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost pPingArgs ownPA b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_uint8 $$ Hb as %v0 %r0 %ok0 Hpost
  unfold decPost
  icases Hpost with (⟨%H0, Hb⟩ | ⟨%a0, %rest0, %H0, %Hown0, Hrest⟩)
  · obtain ⟨H0, rfl⟩ := H0
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pPingArgs, H0], rfl⟩
  obtain ⟨H0, rfl⟩ := H0
  subst Hown0
  wp_auto
  iapply HΦ; iright; iexists .pingArgs v0, rest0
  iframe Hrest
  isplitr
  · ipureintro; exact ⟨by simp [pPingArgs, H0], rfl⟩
  unfold ownPA
  ipureintro; rfl

theorem wp_rpcDec_defs_BeTheLeaderReply (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_defs_BeTheLeaderReply)) (Val #b))
    {{ (v : replica.defs.BeTheLeaderReply) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost pBeTheLeaderReply ownBTLR b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_int32 $$ Hb as %v0 %r0 %ok0 Hpost
  unfold decPost
  icases Hpost with (⟨%H0, Hb⟩ | ⟨%a0, %rest0, %H0, %Hown0, Hrest⟩)
  · obtain ⟨H0, rfl⟩ := H0
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pBeTheLeaderReply, H0], rfl⟩
  obtain ⟨H0, rfl⟩ := H0
  subst Hown0
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_apply wp_rpcDec_int32 $$ Hr as %v1 %r1 %ok1 Hpost
  unfold decPost
  icases Hpost with (⟨%H1, Hr⟩ | ⟨%a1, %rest1, %H1, %Hown1, Hrest⟩)
  · obtain ⟨H1, rfl⟩ := H1
    ihave Hb := Hback $$ Hr
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pBeTheLeaderReply, H0, H1], rfl⟩
  obtain ⟨H1, rfl⟩ := H1
  subst Hown1
  ihave Hrest := restOf_comp $$ Hback Hrest
  wp_auto
  iapply HΦ; iright; iexists .beTheLeaderReply v0 v1, rest1
  iframe Hrest
  isplitr
  · ipureintro; exact ⟨by simp [pBeTheLeaderReply, H0, H1], rfl⟩
  unfold ownBTLR
  ipureintro; rfl

theorem wp_rpcDec_defs_GetLeaderArgs (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_defs_GetLeaderArgs)) (Val #b))
    {{ (v : replica.defs.GetLeaderArgs) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost (pEmpty .getLeaderArgs) (ownEmpty .getLeaderArgs) b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  ihave Hrest := restOf_refl $$ Hb
  iapply HΦ; unfold decPost; iright; iexists .getLeaderArgs, bs
  iframe Hrest
  unfold ownEmpty
  ipureintro; exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem wp_rpcDec_defs_GetReplicaListArgs (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_defs_GetReplicaListArgs)) (Val #b))
    {{ (v : replica.defs.GetReplicaListArgs) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost (pEmpty .getReplicaListArgs) (ownEmpty .getReplicaListArgs) b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  ihave Hrest := restOf_refl $$ Hb
  iapply HΦ; unfold decPost; iright; iexists .getReplicaListArgs, bs
  iframe Hrest
  unfold ownEmpty
  ipureintro; exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem wp_rpcDec_defs_PingReply (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_defs_PingReply)) (Val #b))
    {{ (v : replica.defs.PingReply) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost (pEmpty .pingReply) (ownEmpty .pingReply) b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  ihave Hrest := restOf_refl $$ Hb
  iapply HΦ; unfold decPost; iright; iexists .pingReply, bs
  iframe Hrest
  unfold ownEmpty
  ipureintro; exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem wp_rpcDec_defs_BeTheLeaderArgs (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_defs_BeTheLeaderArgs)) (Val #b))
    {{ (v : replica.defs.BeTheLeaderArgs) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost (pEmpty .beTheLeaderArgs) (ownEmpty .beTheLeaderArgs) b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  ihave Hrest := restOf_refl $$ Hb
  iapply HΦ; unfold decPost; iright; iexists .beTheLeaderArgs, bs
  iframe Hrest
  unfold ownEmpty
  ipureintro; exact ⟨⟨rfl, rfl⟩, rfl⟩

end wps

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
