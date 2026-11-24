/-
The proofs of the paxos kit's functions (`kit.go`, notes/dsv-paxos.md), from their callees' specs
(remote's, the paxos package's), taken as hypotheses.
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.ModelSet
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient
public import Perennial.Spec.time.Sleep
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

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
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]

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


theorem Codec.wp_proof : Codec.spec (GF := GF) (hG := hG) := by
  intro Γ
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold codecOk woR
  simp only
  isplitr
  · -- EncIn
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
    iapply HΦ'
    iexact Hsl
  isplitr
  · -- DecIn
    iintro %i %b %dq
    iintro !> %Φ' Hb HΦ'
    wp_auto
    wp_apply wp_bytes_to_string $$ [Hb] as Hb
    · iexact Hb
    iapply HΦ'
    ipureintro
    intro _
    rfl
  isplitr
  · -- EncOut
    iintro %v %Hv
    obtain ⟨u, w, rfl⟩ : ∃ (u : Bool) (w : BStr), v = outV u w.1 := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, _, h⟩
      · exact ⟨_, ⟨[], by simp⟩, h⟩
    iintro !> %Φ' - HΦ'
    rw [encOutV_outV]
    have hw := w.2
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
    wp_apply (wp_slice_make3 (V := w8) (W64 1) (W64 1 + W64 w.1.length) (by word))
      as %b ⟨Hb, Hcap, -⟩
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      obtain ⟨h1, h2⟩ := Hbl; simp only [List.length_replicate] at h1; word
    cases u
    · wp_auto
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
      iapply HΦ'
      simp only [encOutB, Bool.false_eq_true, ↓reduceIte]
      rw [show List.replicate 1 (zero_val w8) ++ w.val = W8 0 :: w.val from rfl]
      iexact Hb'
    · wp_auto
      rw [ite_eq_left h0]
      wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (W8 1) $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      wp_auto
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
      iapply HΦ'
      simp only [encOutB, ↓reduceIte]
      rw [show (List.replicate 1 (zero_val w8)).set 0 (W8 1) ++ w.val = W8 1 :: w.val from rfl]
      iexact Hb'
  isplitr
  · -- DecOut
    iintro %v %b %dq %Hv
    obtain ⟨u, w, rfl⟩ : ∃ (u : Bool) (w : BStr), v = outV u w.1 := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, _, h⟩
      · exact ⟨_, ⟨[], by simp⟩, h⟩
    iintro !> %Φ' Hb HΦ'
    rw [encOutV_outV]
    simp only [encOutB]
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    have hw := w.2
    have hb1 : 1 ≤ sint.Z b.len := by
      obtain ⟨h1, h2⟩ := Hlen; simp only [List.length_cons] at h1
      have h3 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := Int.toNat_of_nonneg h2
      omega
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      constructor <;> word
    wp_auto
    wp_if_destruct
    · exfalso; word
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if u then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_if_destruct
    · exfalso; cases u <;> simp only [Bool.false_eq_true, ↓reduceIte] at Hif <;> word
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if u then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap from ⟨by word, by word, Hwf.2⟩)]
    icases (ownSlice_split_all (W64 1) b dq _ ⟨by word, by word⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
    rw [show sint.nat (W64 1) = 1 from rfl, List.drop_one, List.tail_cons]
    wp_apply wp_bytes_to_string $$ [Hb2] as Hb2
    · iexact Hb2
    iapply HΦ'
    ipureintro
    intro _
    cases u <;> rfl
  isplitr
  · -- IsRead
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    rw [show (!woB.isWrite i) = false from rfl]
    iapply HΦ'
    itrivial
  isplitr
  · -- Unknown
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial
  isplitr
  · -- IsUnknown, an output
    iintro %o
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial
  · -- IsUnknown, an unknown output
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial

/-! ## Masks, injectivity, the model's decoder -/

theorem pendN_paxos : (↑pendN : CoPset) ⊆ ⊤ \ paxosEop := by
  intro p hp
  have h1 := nclose_subseteq (nroot.@"remote") "pend" p hp
  rw [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, ?_⟩
  unfold paxosEop paxosN slotsN
  rw [LawfulSet.mem_union]
  rintro (h | h)
  · exact ndot_ne_disjoint nroot (show "remote" ≠ "paxos" by decide) p ⟨h1, h⟩
  · exact ndot_ne_disjoint nroot (show "remote" ≠ "paxos_slot" by decide) p ⟨h1, h⟩

theorem lintestN_paxos :
    (↑EtcdGrove.lintest.lintestN : CoPset) ⊆ ⊤ \ (paxosEop ∪ ↑pendN) := by
  intro p hp
  change p ∈ (↑(nroot.@"lintest") : CoPset) at hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_union, not_or]
  refine ⟨CoPset.mem_full, ?_, ?_⟩
  · unfold paxosEop paxosN slotsN
    rw [LawfulSet.mem_union]
    rintro (h | h)
    · exact ndot_ne_disjoint nroot (show "lintest" ≠ "paxos" by decide) p ⟨hp, h⟩
    · exact ndot_ne_disjoint nroot (show "lintest" ≠ "paxos_slot" by decide) p ⟨hp, h⟩
  · intro h
    have h1 := nclose_subseteq (nroot.@"remote") "pend" p h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "remote" by decide) p ⟨hp, h1⟩

/-- Distinct outputs have distinct bytes. -/
theorem woR_encOut_inj (Γ : Names) (o o' : BStr)
    (h : (woR (Gg := hG.goose_globalGS) Γ).encOut ((woR (Gg := hG.goose_globalGS) Γ).ov o) =
      (woR (Gg := hG.goose_globalGS) Γ).encOut ((woR (Gg := hG.goose_globalGS) Γ).ov o')) :
    o = o' := by
  simp only [woR, encOutV_outV, encOutB] at h
  exact Subtype.ext (List.cons.inj h).2

/-- The empty string, bounded. -/
def bEmpty : BStr := ⟨[], by simp⟩

/-- **porcupine's model is the pending-writes model** of the far side's store `woR Γ`. -/
theorem woS_pendDec (Γ : Names) : PendDec (woR (Gg := hG.goose_globalGS) Γ) (woS (GF := GF)) where
  init := rfl
  ok s i o := linkv.pM_step woB woDec s _ i _ (woDec_box i false o)
  err s i := linkv.pM_step woB woDec s _ i _ (woDec_box i true bEmpty)
  ioOk_ok i o := BI.pure_intro ⟨⟨i, rfl⟩, false, o, rfl⟩
  ioOk_err i := BI.pure_intro ⟨⟨i, rfl⟩, true, bEmpty, rfl⟩
  noObs _ := rfl

theorem Gen.wp_proof : Gen.spec (GF := GF) (hG := hG) := by
  unfold Gen.spec EtcdGrove.lintest.genSpec
  iintro %id
  wp_start as _
  wp_auto
  wp_if_destruct
  · iapply HΦ; imodintro; ipureintro; exact ⟨⟨go!"v1", by decide⟩, rfl⟩
  wp_if_destruct
  · iapply HΦ; imodintro; ipureintro; exact ⟨⟨go!"v2", by decide⟩, rfl⟩
  wp_if_destruct
  · iapply HΦ; imodintro; ipureintro; exact ⟨⟨go!"v3", by decide⟩, rfl⟩
  iapply HΦ; imodintro; ipureintro; exact ⟨⟨go!"v4", by decide⟩, rfl⟩

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

theorem pendCtx_woS (Γ : Names) (γp : PendNames) :
    pendCtx (Gg := hG.goose_globalGS) (woR Γ) (woS0 (GF := GF)) γp =
      pendCtx (Gg := hG.goose_globalGS) (woR Γ) (woS (GF := GF)) γp := rfl

theorem pendLib_woS (γp : PendNames) :
    pendLib (Gg := hG.goose_globalGS) (woS0 (GF := GF)) γp (woS0 (GF := GF)).M.init =
      pendLib (Gg := hG.goose_globalGS) (woS (GF := GF)) γp (woS (GF := GF)).M.init := rfl

theorem Orch.wp_proof (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (wp_Check : github_com.mit_pdos.etcd_grove.examples.lib.remote.Check.spec (GF := GF) (hG := hG)
      (St := Option GoString) (I := BStr) (O := BStr)) :
    Orch.spec (GF := GF) (hG := hG) := by
  intro Γ γp hrb
  rw [pendCtx_woS, pendLib_woS]
  wp_start as ⟨#Hra, #Hmap, #Hpend, Hlib, Hbud⟩
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
  wp_apply wp_Check (woR Γ) woS γp m addrs clientAddrs cd _ (W64 1) d pendN_paxos lintestN_paxos (woS_pendDec Γ) (woR_encOut_inj Γ)
    (fun st => woR_timeless Γ st) hrb (by rw [hlen']; decide) (by decide)
    (by rw [hlen']; decide) 3 (by decide) $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
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
    iintro !> %Φr ⟨%Hsys, HL, -⟩ HΦr
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
    iintro %Φr HΦr
    wp_auto
    iapply HΦr
    ipureintro; rfl

end proof

end github_com.xiang90.paxos.examples.paxosnet
end Perennial
