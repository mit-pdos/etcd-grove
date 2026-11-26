/-
The replica's rpc methods (`NetRpc/Specs.lean`'s `replicaBtl.spec`, `replicaPing.spec`) for the
epaxos replica handle `isReplica γ i`: `(*Replica).BeTheLeader` (`epaxos.go`: under the instance
lock, `IsLeader = true`, the model's `beTheLeader` step `ep_beTheLeader`; then `r.Println`;
returns `nil`, the reply untouched) and `(*Replica).Ping` (the framework's, promoted through the
embedded `*replica.Replica`: returns `nil`, nothing touched). Ported from the lab's
`Interface/Epaxos.lean` (`wp_BeTheLeader`, `wp_Ping`); dlog's `Println` is a hypothesis.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Log
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.EpaxosGhost
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.imdea_software.swiftpaxos_epaxos

open github_com.imdea_software.swiftpaxos_epaxos.kvs model epaxosProof

section rpc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [examples.epaxosnet.Assumptions] [master.Assumptions] [epaxos.Assumptions]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
  [TH : StateTreemap GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `(*Replica).BeTheLeader(args, reply)`. -/
theorem replicaBtl_holds (hP : dlog.Logger.Println.spec (GF := GF)) (γ : EpNames) (i : Nat) :
    replicaBtl.spec (isReplica (GF := GF) γ i) := by
  intro r pa pr
  rw [isReplica_unseal]
  wp_start as ⟨#Hisr, Hpa, Hreply⟩
  unfold isReplicaDef
  icases Hisr with ⟨%rr, %L, %p, #Hrr, #Hro, %HL, #Hep, ⟨%lp, #Hlp, #Hlock⟩, #Hinv, #Hpk⟩
  ihave ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hro
  have hi : i < nR := by have := HLn.1; have := HLn.2; simp only [nRep, nR] at *; omega
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
  unfold instLockInv
  icases HL with ⟨⟨%σ, Hrep, Hfrag, Hidle⟩, Hstack⟩
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib, %Hcb, Hinsts, Hcrt, Hcut, Heut, Hconf, Hmsk, Hls, Hlpt, HmaxSeq, Hlead,
    Hmrb, Hstore, Hpeer⟩
  wp_auto_lc 1
  have hb : ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ £ 1 ={⊤}=∗
      repFrag γ i (hBeTheLeader σ) :=
    ep_beTheLeader γ ⊤ i σ (by solve_ndisj) hi
  iapply fupd_wp
  imod hb $$ Hinv Hfrag Hlc1 with Hfrag
  imodintro
  wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hlead Hinsts Hcrt Hcut Heut Hconf Hmsk Hls
    Hlpt HmaxSeq Hmrb Hstore Hpeer Hfrag Hidle Hstack]
  · iframe Hstack
    iexists hBeTheLeader σ
    iframe Hfrag Hidle
    unfold hBeTheLeader
    iframe Hlead Hinsts Hcrt Hcut Heut Hconf Hmsk Hls Hlpt HmaxSeq Hmrb Hstore Hpeer
    ipureintro; exact ⟨Hib, Hcb⟩
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply (wp_ep_Println hP γ r rr i L p) $$ [$Hrr $Hro]
  wp_end

/-- `(*Replica).Ping(args, reply)`. -/
theorem replicaPing_holds (γ : EpNames) (i : Nat) : replicaPing.spec (isReplica (GF := GF) γ i) := by
  intro r pa pr a
  rw [isReplica_unseal]
  wp_start as ⟨#Hisr, Hpa, Hreply⟩
  unfold isReplicaDef
  icases Hisr with ⟨%rr, %L, %p, #Hrr, #Hro, %HL, #Hep, ⟨%lp, #Hlp, #Hlock⟩, #Hinv, #Hpk⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_end

end rpc

end github_com.imdea_software.swiftpaxos_epaxos

end Perennial
