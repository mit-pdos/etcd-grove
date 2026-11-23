/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/network/NewTCP.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension. `events.Event.FromDecoder`'s spec (the events
package's, `Spec/events.lean`) is the theorem's hypothesis `wp_FromDecoder` (the lab linked its
proof); the configured address is `VsrWire.addrs`'s (`ipv4port.addrs`, the same list).
-/
/-
`NewTCP`: the `*TCP`, its ghost state, its lock, its registry, its sender's right.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Ghost
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.queue.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.ipv4port.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.assert.Results
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section helpers
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions]

theorem network.quarters : ((1 : Qp).half + (1 : Qp).half.half) + (1 : Qp).half.half = 1 := by
  apply Subtype.ext; simp; grind

theorem network.split_quarters (l : Loc) (v : Loc) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢
      typedPointsto l v (DFrac.own ((1 : Qp).half + (1 : Qp).half.half)) ∗
      typedPointsto l v (DFrac.own (1 : Qp).half.half) := by
  have h := (typedPointsto_frac_add (GF := GF) l v
    ((1 : Qp).half + (1 : Qp).half.half) (1 : Qp).half.half).1
  rw [network.quarters] at h
  exact h

/-- One reader slot of a fresh lock, and its guard. -/
theorem network.one_slot (rw : Loc) (P : Qp → IProp GF) :
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        sync.ownRWMutex rw P) ⊢
      sync.ownRWMutex rw P ∗ sync.isRWMutexGuard rw P := by
  have h2 := sync.actualMaxReaders_ge_2
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [hm, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨Htok, -⟩
  iapply sync.ownRWMutex_guard $$ Htok

end helpers

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF] [models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true

theorem network.NewTCP.wp_proof
    (wp_FromDecoder : events.Event.FromDecoder.spec (GF := GF) (hG := hG)) :
    network.NewTCP.spec (GF := GF) (hG := hG) := by
  intro F me γ hme
  wp_start as ⟨#Hfd, #Hcs, #Hkit, #Hnv⟩
  iapply wp_fupd
  wp_auto
  wp_apply ipv4port.IPv4Port.FromHostPort.wp _ _ me (by exact hme) $$ [$ipv4port] as ⟨%ip, ipv4port, #Hcfg⟩
  wp_apply assert.Assert.wp
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %cm Hcm
  wp_apply (wp_map_make1 (K := GoString) (V := Bool)) as %sm Hsm
  imod (ghost_map_alloc_empty (GF := GF) (K := Loc) (V := network.ConnRec)) with ⟨%γr, HR⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Unit)) with ⟨%γh, HT⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Unit)) with ⟨%γd, HD⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Unit)) with ⟨%γs, HS⟩
  let ns : network.TcpNames := ⟨γr, γh, γd, γs, γ⟩
  wp_apply queue.New.wp events.NetworkEvent.ty (network.evOk ns) as %q #Hq
  iStructNamed «$r0»
  icases network.split_quarters _ _ $$ mu with ⟨mu34, mu14⟩
  ipersist mu14
  ipersist ip
  ipersist conns
  ipersist srcs
  ipersist queue
  imod inv_alloc (network.rootN ns) ⊤ iprop(∃ mu' : Loc,
      typedPointsto (network.muField «$r0_ptr») mu' (DFrac.own ((1 : Qp).half + (1 : Qp).half.half)))
    $$ [mu34] with #Hroot0
  · inext; iexists _; iexact mu34
  ihave #Hroot : network.rootInv «$r0_ptr» ns $$ []
  · unfold network.rootInv; iexact Hroot0
  imod inv_alloc network.regN ⊤ (network.regInv ns) $$ [HR] with #Hreg
  · inext
    unfold network.regInv
    iexists ∅
    iframe HR
    iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2
    itrivial
  imod sync.init_RWMutex (network.lockP ns cm sm) (E := ⊤) «$v3_ptr» $$ [Hcm Hsm HD HS] «$v3»
    with Hslots
  · inext
    iexists ∅, ∅, ∅, ∅
    iframe
    isplitr
    · ipureintro; intro s h; cases h
    isplitr
    · iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2; itrivial
    isplitr
    · iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2; itrivial
    · iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2; itrivial
  icases network.one_slot «$v3_ptr» _ $$ Hslots with ⟨Hown, #Hguard⟩
  ihave #Hrd : network.readerOk γ $$ []
  · unfold network.readerOk
    imodintro
    iintro %ev %dec %e0 %Φ' ⟨Hr, He⟩ HΦr
    wp_apply wp_FromDecoder F γ ev dec e0 $$ [$Hr $He $Hfd $Hcs $Hkit]
      as %err ⟨Hr, #HerrOk, Hres⟩
    iapply HΦr
    iframe
    iexact HerrOk
  imodintro
  iapply HΦ
  isplitl []
  · unfold network.isTCP network.isTCPDef network.tcpCore network.fieldsRO
    iexists ns, { ip' := ip, conns' := cm, srcs' := sm, queue' := q, mu' := «$v3_ptr» }
    iframe Hcfg Hrd Hroot Hreg Hq Hguard ip conns srcs queue mu14 Hnv
    ipureintro; rfl
  · unfold network.tcpSender network.tcpSenderDef network.fieldsRO
    iexists ns, { ip' := ip, conns' := cm, srcs' := sm, queue' := q, mu' := «$v3_ptr» }, ∅
    iframe Hown HT Hroot ip conns srcs queue mu14
    iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2
    itrivial

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
