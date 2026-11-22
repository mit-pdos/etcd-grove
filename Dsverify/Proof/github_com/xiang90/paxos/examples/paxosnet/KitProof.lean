/-
The proofs of the paxos kit's functions (`kit.go`, notes/dsv-paxos.md), from their callees' specs
(remote's, the paxos package's), taken as hypotheses.
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.Kit
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient
public import Perennial.Spec.time.Sleep

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.xiang90.paxos.examples.paxosnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.xiang90.paxos.examples.paxosnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

local notation "kpkg" => pkg_id.github_com.xiang90.paxos.examples.paxosnet

set_option goose.wp.extras true

/-- `PaxosAddrs()` returns a new slice of the paxos deployment's addresses. -/
theorem wp_PaxosAddrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.PaxosAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* github_com.xiang90.paxos.addrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) github_com.xiang90.paxos.addrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `ClientAddrs()` returns a new slice of the client machines' addresses. -/
theorem wp_ClientAddrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.ClientAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* clientAddrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) clientAddrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `attempt()`: some duration. -/
theorem wp_attempt :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.attempt)) (Val #()))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

theorem Model.wp_proof : Model.spec (GF := GF) (hG := hG) := by
  sorry

theorem Codec.wp_proof : Codec.spec (GF := GF) (hG := hG) := by
  sorry

theorem Gen.wp_proof : Gen.spec (GF := GF) (hG := hG) := by
  sorry

theorem Server.wp_proof (wp_RunServer : RunServer.spec (GF := GF) (hG := hG)) :
    Server.spec (GF := GF) (hG := hG) := by
  intro Γ id hid
  wp_start as ⟨#Hpx, #Hprotos, Hst⟩
  ihave #Hpp : isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_PaxosAddrs as %sl Hsl
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  imodintro
  simp only [github_com.xiang90.paxos.examples.paxosnet.NAcceptors,
    github_com.xiang90.paxos.examples.paxosnet.NLearners, github_com.xiang90.paxos.examples.paxosnet.NC]
  wp_apply wp_RunServer Γ sl id hid $$ [Hst] as %hf
  · iframe Hpx Hsl Hprotos Hst
  exact hf.elim

theorem Orch.wp_proof (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (hdec : ∀ Γ : Names, PendDec (woR (Gg := hG.goose_globalGS) Γ) (woS (GF := GF)))
    (wp_Check : github_com.mit_pdos.etcd_grove.examples.lib.remote.Check.spec (GF := GF) (hG := hG)
      (St := Option GoString) (I := BStr) (O := BStr)) :
    Orch.spec (GF := GF) (hG := hG) := by
  intro Γ γp hrb
  wp_start as ⟨#Hra, #Hmap, #Hpend, Hlib⟩
  ihave #Hcc : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_apply wp_Model as %m #Hm
  wp_apply wp_ClientAddrs as %addrs Haddrs
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Haddrs with #Haddrs
  imodintro
  wp_apply (wp_Codec Γ) as %cd #Hcd
  wp_apply wp_attempt as %d -
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hlen' : sint.Z addrs.len = 4 := by
    have := Hal.1; simp only [clientAddrs, List.length_cons, List.length_nil] at this; word
  wp_apply wp_Check (woR Γ) woS γp m addrs clientAddrs cd _ (W64 1) d sorry sorry (hdec Γ) sorry
    (fun st => woR_timeless Γ st) hrb (by rw [hlen']; decide) (by decide)
    (by rw [hlen']; decide) $$ [Hlib]
  · iframe #
    iframe Hlib
    iapply (show ⊢ EtcdGrove.lintest.genSpec (GF := GF)
        (functions github_com.xiang90.paxos.examples.paxosnet.Gen [])
        (fun x => iprop(∃ i, ⌜x = (woR (Gg := hG.goose_globalGS) Γ).iv i⌝)) from wp_Gen)
  iapply HΦ
  itrivial

theorem Client.wp_proof (wp_NewNetCluster : NewNetCluster.spec (GF := GF) (hG := hG))
    (wp_Propose : NetCluster.Propose.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_ServeClient : github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient.spec
      (GF := GF) (hG := hG) (I := BStr) (O := BStr)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro Γ c hc
  wp_start as ⟨#Hpx, #Hprotos, Htok, #Hra, #Hmap⟩
  ihave #Hpp : isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos $$ []
  · iPkgInit
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_PaxosAddrs as %sl Hsl
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  imodintro
  simp only [github_com.xiang90.paxos.examples.paxosnet.NAcceptors,
    github_com.xiang90.paxos.examples.paxosnet.NLearners, github_com.xiang90.paxos.examples.paxosnet.NC]
  wp_apply wp_NewNetCluster Γ sl c hc $$ [Htok] as %cl #Hcl
  · iframe Hpx Hsl Hprotos Htok
  irename cl => Hclp
  irename c => Hcp
  ipersist Hclp
  ipersist Hcp
  wp_apply wp_ClientAddrs as %asl Hasl
  ihave %Hal := ownSlice_len _ _ _ $$ Hasl
  have hal : clientAddrs.length = 4 := rfl
  have hb : 0 ≤ sint.Z c ∧ sint.Z c < sint.Z asl.len := by word
  simp only [hb, _root_.and_self, ↓reduceIte]
  list_elem clientAddrs (uint.nat c) as a
  wp_apply wp_load_slice_index asl (sint.Z c) clientAddrs _ a hb.1 $$ [Hasl] with Hasl
  · iframe; ipureintro; rw [show (sint.Z c).toNat = uint.nat c by word]; exact Ha_lookup
  have ha : a = clientAddrs.getD (uint.nat c) [] := by
    simp [List.getD_eq_getElem?_getD, Ha_lookup]
  subst ha
  wp_auto
  wp_apply (wp_Codec Γ) as %cd #Hcd
  wp_apply wp_attempt as %d -
  wp_apply wp_ServeClient (RBase.svc (Gg := hG.goose_globalGS) (woR Γ)) _ _ _ _ cd d
    (fun sys => iprop(⌜sys = interface.mkOk (go.GoType.PointerType
      github_com.xiang90.paxos.NetCluster.ty) #cl⌝)) $$ [] as ⟨⟩
  iframe #
  isplit
  · iapply codecOk_wireOk $$ Hcd
  isplit
  · -- the operation: client `c`'s proposal
    iapply opMaybe_svcOp
    unfold opMaybe
    iintro %sys %i %Φo
    iintro !> %Φr ⟨%Hsys, HL⟩ HΦr
    subst Hsys
    rw [slotUpd_write _ rfl]
    ihave HAU := lin_opAU Γ i Φo $$ HL
    wp_auto
    wp_apply time.wp_Sleep
    have hi := i.2
    ihave Hwp := wp_Propose Γ cl c (W64 10000) i.1 (fun w => Φo (bnd w i)) hc hi $$ Hpp Hcl HAU
    simp only [github_com.xiang90.paxos.examples.paxosnet.ProposeWaitMs]
    wp_bind (App (App (App (Val (cl @!! go.GoType.PointerType github_com.xiang90.paxos.NetCluster.ty @!! go!"Propose"))
          (Val #c)) (Val #i.1)) (Val #(W64 10000)))
    iapply wp_wand $$ Hwp
    iintro %r Hr
    icases Hr with (⟨%w, ⟨%Hr, %Hw⟩, HQ⟩ | %Hr)
    · subst Hr
      wp_auto
      iapply HΦr
      isplitr
      · ipureintro; first | rfl | trivial
      ileft
      iexists bnd w i
      rw [bnd_of Hw i]
      iframe HQ
      ipureintro; rfl
    · obtain ⟨x, rfl⟩ := Hr
      wp_auto
      iapply HΦr
      isplitr
      · ipureintro; first | rfl | trivial
      iright
      ipureintro; rfl
  · -- the client's system: its node
    iintro !> %Φr - HΦr
    wp_auto
    iapply HΦr
    ipureintro; rfl

end proof

end github_com.xiang90.paxos.examples.paxosnet
end Perennial
