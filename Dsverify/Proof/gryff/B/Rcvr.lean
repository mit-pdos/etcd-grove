/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Rcvr.lean (run gryff-bump-1, lab
master 915f964; notes/dsv-gryff.md).

Unit B3: a replica is the `"Replica"` service's receiver (`replicaOk`): `Ping` and `BeTheLeader`
(`genericsmr.Replica`'s, promoted through the embedded `*genericsmr.Replica`) return `nil`.

Port (`Net/`): the lab's `rcvrOk` over its codec's dispatch is `Net/`'s receiver: the kit's
`rpcReceiver` gives the replica's `Receiver` (`RcvLaws.rcv_Replica`) from each method's `NewArg`
obligation (`newArg_Ping`, `newArg_BeTheLeader`: the argument decodes into `NewArg()`'s fresh
value, the call returns `nil`, the reply encodes into the deposit's answer).
-/
module

public import Dsverify.Proof.gryff.Server.SpecsDefs
public import Dsverify.Proof.gryff.examples.gryffnet.Base
public import Dsverify.Proof.gryff.src.gryff.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions]

set_option goose.wp.extras true

theorem replica_Ping_wp (rep gR ap pp : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        rep.[src.gryff.Replica, go!"Replica"] ↦□ gR }}
      (App (App (Val (rep @!! go.GoType.PointerType src.gryff.Replica.ty @!! go!"Ping"))
        (Val #ap)) (Val #pp))
    {{ RET #interface.nil; True }} := by
  wp_start as #HgR
  ihave #Hgs : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
  · iPkgInit
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_end

theorem replica_BeTheLeader_wp (rep gR ap pp : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        rep.[src.gryff.Replica, go!"Replica"] ↦□ gR }}
      (App (App (Val (rep @!! go.GoType.PointerType src.gryff.Replica.ty @!!
        go!"BeTheLeader")) (Val #ap)) (Val #pp))
    {{ RET #interface.nil; True }} := by
  wp_start as #HgR
  ihave #Hgs : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
  · iPkgInit
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_end

variable [net.rpc.Assumptions] [net.FieldAssumptions]

theorem ping_zero_pt (p : Loc) :
    (p ↦ zero_val src.genericsmrproto.PingArgs : IProp GF) ⊢
      p ↦ src.genericsmrproto.PingArgs.mk (W8 0) := by
  rfl

theorem pingReply_zero_pt (p : Loc) :
    (p ↦ zero_val src.genericsmrproto.PingReply : IProp GF) ⊢
      p ↦ src.genericsmrproto.PingReply.mk := by
  rfl

theorem btl_zero_pt (p : Loc) :
    (p ↦ zero_val src.genericsmrproto.BeTheLeaderArgs : IProp GF) ⊢
      p ↦ src.genericsmrproto.BeTheLeaderArgs.mk := by
  rfl

theorem btlReply_zero_pt (p : Loc) :
    (p ↦ zero_val src.genericsmrproto.BeTheLeaderReply : IProp GF) ⊢
      p ↦ src.genericsmrproto.BeTheLeaderReply.mk := by
  rfl

theorem replicaSvc_ping_shape (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    replicaSvc go!"Ping" args Φ ⊢ ⌜∃ a, args = encPingArgs a⌝ := by
  unfold replicaSvc withErr replicaSvc0
  iintro H
  icases H with ⟨(⟨-, ⟨%a, %ha⟩, -⟩ | ⟨%h, -⟩), -⟩
  · ipureintro; exact ⟨a, ha⟩
  · exfalso; exact absurd h.1 (by decide)

/-- What a `Ping` deposit says of its arguments, and its answers. -/
theorem replicaSvc_ping (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    replicaSvc go!"Ping" args Φ ⊢
      (Φ encPingReply [] ∧ ∀ msg : GoString, ⌜msg ≠ []⌝ -∗ Φ [] msg) ∗
        ⌜∃ a, args = encPingArgs a⌝ := by
  refine (persistent_entails_left (replicaSvc_ping_shape args Φ)).trans ?_
  unfold replicaSvc withErr replicaSvc0
  iintro ⟨H, %Hp⟩
  isplitl
  · isplit
    · icases H with ⟨(⟨-, -, H⟩ | ⟨%h, -⟩), -⟩
      · iexact H
      · exfalso; exact absurd h.1 (by decide)
    · icases H with ⟨-, H⟩
      iexact H
  · ipureintro; exact Hp

theorem replicaSvc_btl_shape (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    replicaSvc go!"BeTheLeader" args Φ ⊢ ⌜args = encBTLArgs⌝ := by
  unfold replicaSvc withErr replicaSvc0
  iintro H
  icases H with ⟨(⟨%h, -⟩ | ⟨%h, -⟩), -⟩
  · exfalso; exact absurd h (by decide)
  · ipureintro; exact h.2

/-- What a `BeTheLeader` deposit says of its arguments, and its answers. -/
theorem replicaSvc_btl (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    replicaSvc go!"BeTheLeader" args Φ ⊢
      (Φ encBTLReply [] ∧ ∀ msg : GoString, ⌜msg ≠ []⌝ -∗ Φ [] msg) ∗ ⌜args = encBTLArgs⌝ := by
  refine (persistent_entails_left (replicaSvc_btl_shape args Φ)).trans ?_
  unfold replicaSvc withErr replicaSvc0
  iintro ⟨H, %Hp⟩
  isplitl
  · isplit
    · icases H with ⟨(⟨%h, -⟩ | ⟨-, H⟩), -⟩
      · exfalso; exact absurd h (by decide)
      · iexact H
    · icases H with ⟨-, H⟩
      iexact H
  · ipureintro; exact Hp

theorem newArg_Ping (L : CodecLaws (GF := GF)) (rep gR : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
      isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗
      rep.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ net.rpc.codecSet gryffCodec ⊢
    newArgOk gryffCodec (ptrIface src.gryff.Replica.ty rep) (replicaSvc go!"Ping") mPing := by
  iintro ⟨#Hpkg, #Hkit, #HgR, #Hcs⟩
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  ihave Hp := ping_zero_pt p $$ Hp
  have hne : ptrIface src.genericsmrproto.PingArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec gryffCodec (ptrIface src.genericsmrproto.PingArgs.ty p)
      (p ↦ src.genericsmrproto.PingArgs.mk (W8 0)) (replicaSvc go!"Ping")
      (fun args _ => iprop(∃ a, ⌜args = encPingArgs a⌝ ∗ p ↦ src.genericsmrproto.PingArgs.mk a))
      $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    ihave ⟨HS, %Hsh⟩ := persistent_entails_left (replicaSvc_ping_shape args Φ) $$ HS
    obtain ⟨a, rfl⟩ := Hsh
    iframe HS
    iapply L.decA_PingArgs
    isplitl [Hp]
    · iexact Hp
    iintro Hp
    iexists a
    iframe Hp
    ipureintro; rfl
  iapply HΨ $$ %_ %_ %_ %hne Hdec [Hp]
  · iexact Hp
  iintro %args %Φ HS ⟨%a, %Hargs, Hp⟩
  ihave ⟨HΦ, -⟩ := replicaSvc_ping args Φ $$ HS
  unfold net.rpc.callObl
  wp_func_call
  wp_call
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  wp_func_call
  wp_call
  wp_auto
  wp_apply (replica_Ping_wp rep gR p «$r0_ptr»)
  · iframe #
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  ihave Hr := pingReply_zero_pt «$r0_ptr» $$ «$r0»
  iapply L.enc_PingReply
  iframe Hr
  iintro -
  icases HΦ with ⟨HΦ, -⟩
  iexact HΦ

theorem newArg_BeTheLeader (L : CodecLaws (GF := GF)) (rep gR : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
      isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗
      rep.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ net.rpc.codecSet gryffCodec ⊢
    newArgOk gryffCodec (ptrIface src.gryff.Replica.ty rep) (replicaSvc go!"BeTheLeader")
      mBeTheLeader := by
  iintro ⟨#Hpkg, #Hkit, #HgR, #Hcs⟩
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  ihave Hp := btl_zero_pt p $$ Hp
  have hne : ptrIface src.genericsmrproto.BeTheLeaderArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec gryffCodec (ptrIface src.genericsmrproto.BeTheLeaderArgs.ty p)
      (p ↦ src.genericsmrproto.BeTheLeaderArgs.mk) (replicaSvc go!"BeTheLeader")
      (fun _ _ => iprop(p ↦ src.genericsmrproto.BeTheLeaderArgs.mk)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    ihave ⟨HS, %Hsh⟩ := persistent_entails_left (replicaSvc_btl_shape args Φ) $$ HS
    subst Hsh
    iframe HS
    iapply L.decA_BTLArgs
    iframe Hp
    iintro Hp
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  ihave ⟨HΦ, -⟩ := replicaSvc_btl args Φ $$ HS
  unfold net.rpc.callObl
  wp_func_call
  wp_call
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  wp_func_call
  wp_call
  wp_auto
  wp_apply (replica_BeTheLeader_wp rep gR p «$r0_ptr»)
  · iframe #
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  ihave Hr := btlReply_zero_pt «$r0_ptr» $$ «$r0»
  iapply L.enc_BTLReply
  iframe Hr
  iintro -
  icases HΦ with ⟨HΦ, -⟩
  iexact HΦ

/-- `replicaOk` from the embedded generic replica's field (the lab's `replicaOk_intro`). -/
theorem replicaOk_intro (L : CodecLaws (GF := GF)) (RL : RcvLaws (GF := GF))
    (γ : GryffNames GF) (rep gR : Loc) (hrep : rep ≠ null) :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
      isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗
      rep.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ net.rpc.codecSet gryffCodec ⊢
    replicaOk γ rep := by
  iintro #H
  unfold replicaOk
  iapply RL.rcv_Replica rep _ hrep
  isplitr
  · iapply newArg_BeTheLeader L rep gR $$ H
  · iapply newArg_Ping L rep gR $$ H

end

end Perennial.gryff.unitB
