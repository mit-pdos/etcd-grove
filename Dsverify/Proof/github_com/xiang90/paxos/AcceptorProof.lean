/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/AcceptorProof.lean (lab master 7a84fb35; notes/dsv-paxos.md).

The acceptor (`acceptor.go`): `newAcceptor` and `acceptor.run`, over the transport's specs
(hypotheses) and the Paxos hub's laws (package accept-learn).
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.MsgMethods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace github_com.xiang90.paxos

attribute [local instance] GooseGlobalGS.gooseInvGS

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]

/-- The acceptor's protocol state and the fields that mirror it, with its accepted message
`acc` exposed. -/
def accCoreAt (Γ : Names) (ap : Loc) (id : w64) (acc : message) : IProp GF :=
  iprop(∃ (s : AccState) (prom : GoInterface),
    "Hst" ∷ stOwn Γ id s ∗ "Hid" ∷ ap.[acceptor, go!"id"] ↦ id ∗
    "Hacc" ∷ ap.[acceptor, go!"accept"] ↦ acc ∗ "Hprom" ∷ ap.[acceptor, go!"promised"] ↦ prom ∗
    "%Hcore" ∷ ⌜acc.n' = s.k ∧ acc.value' = s.w ∧ msgWf acc ∧
      ∃ pm : message, prom = interface.mkOk message.ty #pm ∧ pm.n' = s.p⌝)

def accCore (Γ : Names) (ap : Loc) (id : w64) : IProp GF :=
  iprop(∃ acc : message, accCoreAt Γ ap id acc)

end defs

section proofs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]
variable [package_sem : paxos.Assumptions] [field_sem : net.FieldAssumptions]

set_option goose.wp.extras true

local notation "pkg" => pkg_id.github_com.xiang90.paxos

theorem newAcceptor.wp_proof : newAcceptor.spec (GF := GF) (hG := hG) :=
  fun Γ id nt nd amap ids lsl hid => by
  wp_start as ⟨Henv, Hst, #Hl⟩
  wp_auto
  iStructNamed «$r0»
  iapply HΦ
  unfold own_acceptor
  iexists nt, nd, amap, ids, lsl, AccState.init, zero_val message,
    interface.mkOk message.ty #(zero_val message)
  iframe
  isplitr
  · ipureintro; exact hid
  isplitr
  · iexact Hl
  ipureintro
  refine ⟨rfl, rfl, ?_, _, rfl, rfl⟩
  change (([] : GoString).length : Int) < 2 ^ 48
  simp

/-- `a.receivePrepare(prepare)`: a promise to the proposer (meeting `msgOK`), or nothing. -/
theorem wp_receivePrepare (Γ : Names) (ap : Loc) (id : w64) (prepare : message)
    (hid : id ∈ accIds) (hfrom : prepare.from' ∈ propIds) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ isPaxos Γ ∗ accCore Γ ap id }}
    (App (Val (ap @!! go.GoType.PointerType acceptor.ty @!! go!"receivePrepare")) (Val #prepare))
  {{ (r : message) (ok : Bool), RET (PairV #r #ok); accCore Γ ap id ∗
      if ok then msgOK Γ r ∗ ⌜msgWf r⌝ else True }} := by
  wp_start as ⟨#Hinv, Hc⟩
  iNamed Hc
  obtain ⟨Hk, Hw, Hwf, pm, rfl, Hp⟩ := Hcore
  wp_auto
  wp_apply AccLrn.wp_number
  wp_apply AccLrn.wp_number_ptr $$ [$prepare] as prepare
  wp_if_destruct
  · wp_apply AccLrn.wp_number
    wp_apply AccLrn.wp_ints3
    iintro %sl Hargs
    wp_auto
    wp_apply log.wp_Printf _ _ _ _ (AccLrn.intArgs_wf _) $$ [$Hargs] as -
    iapply HΦ
    isplitl [Hst Hid Hacc Hprom]
    · unfold accCore accCoreAt
      iexists acc, s, _
      iframe
      ipureintro; exact ⟨Hk, Hw, Hwf, pm, rfl, Hp⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · have hlt : sint.Z s.p < sint.Z prepare.n' := by rw [← Hp]; word
    ihave Hup := inv_promise Γ ⊤ id prepare.n' s (by solve_ndisj) hlt $$ Hinv
    iapply fupd_wp
    imod Hup $$ Hst with ⟨Hst, #Hpf⟩
    imodintro
    wp_apply AccLrn.wp_number
    wp_apply AccLrn.wp_ints3
    iintro %sl Hargs
    wp_auto
    wp_apply log.wp_Printf _ _ _ _ (AccLrn.intArgs_wf _) $$ [$Hargs] as -
    wp_apply AccLrn.wp_number
    iapply HΦ
    isplitl [Hst Hid Hacc Hprom]
    · unfold accCore accCoreAt
      iexists acc, _, _
      iframe
      ipureintro; exact ⟨Hk, Hw, Hwf, prepare, rfl, rfl⟩
    · simp only [↓reduceIte]
      unfold msgOK
      simp only [AccLrn.prop_not_acc hfrom, hfrom, ↓reduceIte]
      rw [Hk, Hw]
      isplitl []
      · isplitl []
        · ipureintro; exact ⟨trivial, hid⟩
        · iexact Hpf
      · ipureintro; rw [msgWf] at Hwf ⊢; rw [← Hw]; exact Hwf

/-- `a.receivePropose(propose)`: accepts the issued proposal at its promise (`true`, witnessed),
or ignores it (`false`); never panics, since a `Propose` comes with a promise of its number. -/
theorem wp_receivePropose (Γ : Names) (ap : Loc) (id : w64) (propose : message) (k : w64)
    (w : GoString) (hwf : msgWf propose) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ isPaxos Γ ∗ accCore Γ ap id ∗
      propW Γ propose.n' propose.value' ∗ pfW Γ id propose.n' k w }}
    (App (Val (ap @!! go.GoType.PointerType acceptor.ty @!! go!"receivePropose")) (Val #propose))
  {{ (ok : Bool), RET #ok; ∃ acc, accCoreAt Γ ap id acc ∗
      if ok then ⌜acc.typ' = W64 4⌝ ∗ accW Γ id acc.n' acc.value' else True }} := by
  wp_start as ⟨#Hinv, Hc, #Hprop, #Hpf⟩
  iNamed Hc
  obtain ⟨Hk, Hw, Hwf, pm, rfl, Hp⟩ := Hcore
  ihave Hlb := inv_promise_lb Γ ⊤ id propose.n' k w s (by solve_ndisj) $$ Hinv
  iapply fupd_wp
  imod Hlb $$ Hst Hpf with ⟨Hst, %Hle⟩
  imodintro
  wp_auto_lc 2
  wp_apply AccLrn.wp_number
  wp_apply AccLrn.wp_number_ptr $$ [$propose] as propose
  wp_if_destruct
  · wp_apply AccLrn.wp_number
    wp_apply AccLrn.wp_ints3
    iintro %sl Hargs
    wp_auto
    wp_apply log.wp_Printf _ _ _ _ (AccLrn.intArgs_wf _) $$ [$Hargs] as -
    iapply HΦ
    iexists acc
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitl
    · unfold accCoreAt
      iexists s, _
      iframe
      ipureintro; exact ⟨Hk, Hw, Hwf, pm, rfl, Hp⟩
    · itrivial
  · wp_apply AccLrn.wp_number
    wp_apply AccLrn.wp_number_ptr $$ [$propose] as propose
    wp_if_destruct
    · exfalso; rw [Hp] at Hif; omega
    have hn : s.p = propose.n' := by rw [← Hp] at Hle ⊢; word
    ihave Hup := inv_accept Γ id propose.n' propose.value' s hn $$ Hinv
    iapply fupd_wp
    ihave Hlc : £ 2 $$ [Hlc1 Hlc2]
    · iapply (lc_split (n := 1) (m := 1)).2
      isplitl [Hlc1]
      · iexact Hlc1
      · iexact Hlc2
    imod Hup $$ Hlc Hst Hprop with ⟨Hst, #Hacc'⟩
    imodintro
    wp_apply AccLrn.wp_number
    wp_apply AccLrn.wp_ints4
    iintro %sl Hargs
    wp_auto
    wp_apply log.wp_Printf _ _ _ _ (AccLrn.intArgs_wf _) $$ [$Hargs] as -
    rw [show (Accept : val) = #(W64 4) from rfl]
    wp_auto
    iapply HΦ
    iexists _
    simp only [↓reduceIte]
    isplitl
    · unfold accCoreAt
      iexists _, _
      iframe
      ipureintro
      refine ⟨rfl, rfl, ?_, pm, rfl, ?_⟩
      · rw [msgWf] at hwf ⊢; exact hwf
      · rw [Hp]
    · isplitl []
      · ipureintro; rfl
      · iexact Hacc'

theorem acceptor.run.wp_proof (wp_send : tcpNetwork.send.spec (GF := GF) (hG := hG))
    (wp_recv : tcpNetwork.recv.spec (GF := GF) (hG := hG)) :
    acceptor.run.spec (GF := GF) (hG := hG) := fun Γ ap id => by
  wp_start as Hown
  unfold own_acceptor
  icases Hown with ⟨%nt, %nd, %amap, %ids, %lsl, %s, %acc, %prom, Henv, %hid, Hst, Hid, Hl, #Hls,
    Hacc, Hprom, Hnt, %Hcore⟩
  unfold agentEnv
  icases Henv with ⟨#Hinv, #Hnode, Hnet, %hids⟩
  ihave Hc : accCore Γ ap id $$ [Hst Hid Hacc Hprom]
  · unfold accCore accCoreAt
    iexists acc, s, prom
    iframe
    ipureintro; exact Hcore
  wp_auto
  wp_for
  wp_apply (wp_recv (msgOK Γ) nt nd amap ids id _ hids) $$ [$Hnode $Hnet] as %m %ok ⟨Hnet, Hm⟩
  cases ok
  · wp_auto
    wp_for_post
    iframe
  simp only [↓reduceIte]
  unfold inboxP
  icases Hm with ⟨Hok, %Hto, %Hwf⟩
  ihave Hok := AccLrn.msgOK_acc Γ m id Hto hid $$ Hok
  wp_auto
  wp_if_destruct
  · icases Hok with (%Hprep | ⟨%Htyp, #Hprop, %k, %w, #Hpf⟩)
    · exfalso; rw [Hif] at Hprep; exact absurd Hprep.1 (by simp)
    wp_apply (wp_receivePropose Γ ap id m k w Hwf) $$ [$Hinv $Hc $Hprop $Hpf] as %acd ⟨%acc', Hc, Hacd⟩
    cases acd
    · wp_auto
      wp_for_post
      iframe
      unfold accCore; iexists acc'; iexact Hc
    simp only [↓reduceIte]
    icases Hacd with ⟨%Htyp4, #Hacw⟩
    iNamed Hc
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hls
    ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "l" ∷ (∃ x : w64, l_ptr ↦ x) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z lsl.len⌝ : IProp GF) $$ [i l]
    · iexists W64 0
      iframe
      isplitl
      · iexists _; iexact l
      · ipureintro; word
    wp_for HI
    wp_if_destruct
    · have Hif' : sint.Z i < sint.Z lsl.len := by simpa using Hif
      list_elem lrnIds (sint.nat i) as lr
      simp only [Hi.1, Hif', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index lsl (sint.Z i) lrnIds _ lr Hi.1 $$ [$Hls] as -
      · ipureintro; exact Hlr_lookup
      icases l with ⟨%x, l⟩
      wp_auto
      have hlr : lr ∈ lrnIds := List.mem_of_getElem? Hlr_lookup
      ihave #Hmok : msgOK Γ ({ acc' with from' := id, to' := lr } : message) $$ []
      · iapply (AccLrn.msgOK_lrn Γ _ hlr).2
        isplitl []
        · ipureintro; exact ⟨Htyp4, hid⟩
        · iexact Hacw
      wp_apply (wp_send (msgOK Γ) nt nd amap ids id ({ acc' with from' := id, to' := lr } : message))
        $$ [$Hnode $Hnet $Hmok] as Hnet
      · ipureintro; exact Hcore.2.2.1
      wp_for_post
      iframe
      iexists i + W64 1
      iframe
      isplitl
      · iexists _; iexact l
      · ipureintro; word
    · wp_for_post
      iframe
      unfold accCore accCoreAt
      iexists acc', s, prom
      iframe
      ipureintro; exact Hcore
  wp_if_destruct
  · icases Hok with (%Hprep | ⟨%Htyp, -⟩)
    · wp_apply (wp_receivePrepare Γ ap id m hid Hprep.2) $$ [$Hinv $Hc] as %r %pok ⟨Hc, Hr⟩
      cases pok
      · wp_auto
        wp_for_post
        iframe
      simp only [↓reduceIte]
      icases Hr with ⟨#Hrok, %Hrwf⟩
      wp_auto
      wp_apply (wp_send (msgOK Γ) nt nd amap ids id r) $$ [$Hnode $Hnet $Hrok] as Hnet
      · ipureintro; exact Hrwf
      wp_for_post
      iframe
    · exfalso; rw [Hif] at Htyp; exact absurd Htyp (by simp)
  · icases Hok with (%Hprep | ⟨%Htyp, -⟩)
    · exact absurd Hprep.1 Hif
    · exfalso; simp_all

end proofs