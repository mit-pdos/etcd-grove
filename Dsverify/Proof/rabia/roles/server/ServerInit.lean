/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/ServerInit.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/roles/server.ServerInit`.
-/
module

public import Dsverify.Proof.rabia.internal.queue.Spec
public import Dsverify.Proof.rabia.internal.message.SpecPure
public import Dsverify.Proof.rabia.roles.server.Spec
public import Dsverify.Proof.rabia.roles.server.layers.consensus.Spec
public import Dsverify.Proof.rabia.roles.server.Alloc
public import Dsverify.Proof.rabia.internal.ledger.Spec
public import Dsverify.Proof.rabia.roles.server.layers.proxy.Spec
public import Dsverify.Proof.rabia.roles.server.layers.network.Spec
public import Dsverify.Proof.rabia.internal.logger.Spec

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.roles.server.layers.network rabia.roles.server.layers.consensus
  rabia.roles.server.layers.proxy rabia rabia.internal.ledger

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.Assumptions]

/-- `make(ledger.Ledger, int(config.Conf.LenLedger))` (FINDING S-1 closed by the fork's G11:
the `uint32` length is converted to `int` before `make`). -/
theorem wp_make_ledger :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make2 [rabia.internal.ledger.Ledger.ty]))
        (Val #(W64 (uint.Z (W32 10000)))))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* (List.replicate 10000 (zero_val Loc)) ∗ ownSliceCap Loc sl (DFrac.own 1) }} := by
  wp_start
  wp_apply (wp_slice_make3 (V := Loc) (W64 (uint.Z (W32 10000))) (W64 (uint.Z (W32 10000)))
    (by decide)) as %sl ⟨Hsl, Hcap, -⟩
  iapply HΦ
  iframe

theorem confRO_elim (cf : RCfg) : (confRO cf : IProp GF) ⊢
    ∃ ps, (globalAddr Conf ↦□ confVal cf ps : IProp GF) ∗ ps ↦*□ peerStrs cf := by
  unfold confRO; iintro ⟨-, H⟩; iexact H

/-- The recorded configuration is one `choose` picks (unfolds Ghost's `cfgIs`: a missing law). -/
theorem cfgIs_ok (γr : RabiaNames) (cf : RCfg) : (cfgIs γr cf : IProp GF) ⊢ ⌜cf.Ok⌝ := by
  unfold cfgIs; iintro ⟨-, %h⟩; ipureintro; exact h

/-- A fresh slot's resources (`Reset`'s postcondition). -/
def slotRes (L : Nat) (e : SlotV) : IProp GF :=
  iprop(isSlot e.loc e.γ e.q ∗ slotSt e.γ (SlotSt.init L) ∗
    slotPriv e.loc { phase := 0, round := 0, myProp := default, myBC := [] } ∗ queueFresh e.q)

theorem ServerInit.wp_proof (hReset : Slot.Reset.spec (GF := GF))
    (hProxy : ProxyInit.spec (GF := GF)) (hNet : NetworkInit.spec (GF := GF))
    (hCons : ConsensusInit.spec (GF := GF)) : ServerInit.spec (GF := GF) := by
  intro γ cf k id hid hk
  wp_start as ⟨#Hconf, #Hcfg, Hshare⟩
  ihave %hc := cfgIs_ok γ.rab cf $$ Hcfg
  ihave ⟨%cps, #Hc, #Hcps⟩ := confRO_elim cf $$ Hconf
  ihave Hc2 := Hc
  iStructNamedPrefix Hc2 "C"
  wp_auto
  wp_apply (chan.wp_make1 (V := Unit)) as %chDone %γDone ⟨#HchDone, %HcapDone, HoDone⟩
  wp_apply wp_make_ledger as %ledger ⟨Hled, Hledcap⟩
  wp_apply (chan.wp_make1 (V := Command)) as %chC2p %γC2p ⟨#HchC2p, %HcapC2p, HoC2p⟩
  wp_apply (chan.wp_make2 (V := Msg) (W64 500000)) as %chP2n %γP2n ⟨#HchP2n, %HcapP2n, HoP2n⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := Msg) (W64 500000)) as %chN2p %γN2p ⟨#HchN2p, %HcapN2p, HoN2p⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := Msg) (W64 500000)) as %chH2n %γH2n ⟨#HchH2n, %HcapH2n, HoH2n⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := Msg) (W64 500000)) as %chE2n %γE2n ⟨#HchE2n, %HcapE2n, HoE2n⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := Msg) (W64 500000)) as %chX1 %γX1 ⟨-, -, -⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := Msg) (W64 500000)) as %chX2 %γX2 ⟨-, -, -⟩
  · ipureintro; decide
  iStructNamed «$r0»
  wp_apply (chan.wp_make2 (V := Msg) (W64 500000)) as %chN2h %γN2h ⟨#HchN2h, %HcapN2h, HoN2h⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := Msg) (W64 500000)) as %chN2e %γN2e ⟨#HchN2e, %HcapN2e, HoN2e⟩
  · ipureintro; decide
  ihave %Hledlen := ownSlice_len $$ Hled
  ihave HI : (∃ (n : Nat) (slots : List SlotV), "i" ∷ i_ptr ↦ W64 n ∗
      "%Hn" ∷ ⌜n ≤ 10000 ∧ slots.length = n⌝ ∗
      "Hled" ∷ ledger ↦* (slots.map (·.loc) ++ List.replicate (10000 - n) (zero_val Loc)) ∗
      "Hslots" ∷ [∗list] e ∈ slots, slotRes cf.blockLen e) $$ [i Hled]
  · iexists 0, []
    simp only [List.map_nil, List.nil_append, Nat.sub_zero]
    iframe
    isplit
    · ipureintro; simp
    · iapply BigSepL.bigSepL_nil.2; iempintro
  irename : ("_" ∷ (True : IProp GF)) => Hjunk
  iclear Hjunk
  wp_for HI
  wp_if_destruct
  · rename_i sv
    obtain ⟨Hn1, Hn2⟩ := Hn
    have hn : n < 10000 := by
      have : sint.Z (W64 (uint.Z (W32 10000))) = 10000 := by decide
      rw [this] at Hif; word
    have hlen : sint.Z ledger.len = 10000 := by
      obtain ⟨h1, h2⟩ := Hledlen
      simp only [List.length_replicate] at h1
      have : (sint.Z ledger.len).toNat = 10000 := h1.symm
      omega
    have hnz : sint.Z (W64 (n : Int)) = n := by word
    rw [if_pos (by rw [hnz, hlen]; omega)]
    wp_apply (wp_store_slice_index (V := Loc) ledger (sint.Z (W64 (n : Int)))) $$ [Hled] as Hled
    · iframe; ipureintro; rw [hnz]
      simp only [List.length_append, List.length_map, List.length_replicate]; omega
    rw [if_pos (by rw [hnz, hlen]; omega)]
    have hget : (List.map (fun x => x.loc) slots ++ List.replicate (10000 - n) (zero_val Loc)).set
        (sint.Z (W64 (n : Int))).toNat «$r0_ptr» =
        List.map (fun x => x.loc) slots ++ «$r0_ptr» :: List.replicate (10000 - (n + 1)) (zero_val Loc) := by
      rw [hnz]; simp only [Int.toNat_natCast]
      rw [List.set_append_right _ _ (by simp [Hn2])]
      simp only [List.length_map, Hn2, Nat.sub_self]
      obtain ⟨m, hm⟩ : ∃ m, 10000 - n = m + 1 := ⟨10000 - n - 1, by omega⟩
      rw [hm, List.replicate_succ, List.set_cons_zero, show 10000 - (n + 1) = m by omega]
    rw [hget]
    wp_apply (wp_load_slice_index (V := Loc) ledger (sint.Z (W64 (n : Int))) _ _ «$r0_ptr» (by omega))
      $$ [Hled] as Hled
    · iframe; ipureintro; rw [hnz]; simp [Hn2]
    wp_apply +noauto hReset cf «$r0_ptr» $$ [«$r0»] as Hr
    · iframe «$r0»; iframe #
    imod Hr with ⟨%γs, %qs, #Hisl, Hst, Hpriv, Hq⟩
    wp_auto
    wp_for_post
    iframe
    iexists n + 1, slots ++ [⟨«$r0_ptr», γs, qs⟩]
    rw [show W64 (n : Int) + W64 1 = W64 ((n + 1 : Nat) : Int) by word]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append]
    iframe i Hled
    isplit
    · ipureintro; simp [Hn2]; omega
    · iapply BigSepL.bigSepL_snoc.2
      iframe Hslots
      unfold slotRes; iframe; iframe #
  -- the loop is done: the ledger's 10000 slots
  obtain ⟨Hn1, Hn2⟩ := Hn
  have hn : n = 10000 := by
    have : sint.Z (W64 (uint.Z (W32 10000))) = 10000 := by decide
    rw [this] at Hif; word
  subst hn
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
  ipersist Hled
  -- server `k`'s local ghost names
  imod family_alloc (fun _ g => (monoListAuthOwn g 1 ([] : List MsgV) : IProp GF))
    (fun _ => monoList_alloc_nil MsgV) cf.n with ⟨%fpush, Hpush⟩
  imod family_alloc (fun _ g => (ghostMapAuth g 1 (∅ : GMap Nat Unit) : IProp GF))
    (fun _ => ghost_map_alloc_empty) cf.n with ⟨%frcpt, Hrcpt⟩
  imod monoList_alloc_nil (GF := GF) (Nat × Nat) with ⟨%ghlog, Hhlog⟩
  imod monoList_alloc_nil (GF := GF) MsgV with ⟨%gexlog, Hexlog⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%gcrp, Hcrp⟩
  imod prc_alloc (GF := GF) with ⟨%gprc, Hprc⟩
  imod ghostVar_alloc (GF := GF) ([] : List FKey) with ⟨%gkp, Hkp⟩
  imod ghostVar_alloc (GF := GF) ([] : List FKey) with ⟨%gke, Hke⟩
  let γl0 : SrvNames := SrvNames.mk γDone γC2p γP2n γN2p γH2n ⟨γE2n, ghlog, ghlog⟩
    ⟨γN2h, ghlog, ghlog⟩ γN2e frcpt fpush ghlog gexlog gcrp gprc gkp gke slots
  imod start_spsc chE2n (e2nP γ cf k γl0) (fun _ => iprop(False)) γE2n $$ HchE2n [HoE2n]
    with ⟨%se2n, #Hse2n, Hpe2n, Hce2n⟩
  · iright; iexact HoE2n
  imod start_spsc chN2h (n2hP γ cf γl0) (fun _ => iprop(False)) γN2h $$ HchN2h [HoN2h]
    with ⟨%sn2h, #Hsn2h, Hpn2h, Hcn2h⟩
  · iright; iexact HoN2h
  let γl : SrvNames := SrvNames.mk γDone γC2p γP2n γN2p γH2n se2n sn2h γN2e frcpt fpush ghlog
    gexlog gcrp gprc gkp gke slots
  imod start_bag (V := Unit) doneP .Idle chDone γDone trivial $$ HchDone HoDone with #HbDone
  imod start_bag (c2pP γ cf k γl) .Idle chC2p γC2p trivial $$ HchC2p HoC2p with #HbC2p
  imod start_bag (p2nP γ cf k γl) (.Buffered []) chP2n γP2n trivial $$ HchP2n HoP2n with #HbP2n
  imod start_bag n2pP (.Buffered []) chN2p γN2p trivial $$ HchN2p HoN2p with #HbN2p
  imod start_bag (h2nP γ cf) (.Buffered []) chH2n γH2n trivial $$ HchH2n HoH2n with #HbH2n
  imod start_bag (n2eP γ cf k) (.Buffered []) chN2e γN2e trivial $$ HchN2e HoN2e with #HbN2e
  let ch : SrvChans := ⟨chDone, chC2p, chP2n, chN2p, chH2n, chE2n, chN2h, chN2e⟩
  ihave #Hchans : srvChans γ cf k γl ch $$ []
  · unfold srvChans
    iframe #
    rw [show e2nP γ cf k γl = e2nP γ cf k γl0 from rfl, show n2hP γ cf γl = n2hP γ cf γl0 from rfl]
    isplitl
    · iexact Hse2n
    · iexact Hsn2h
  -- the slots: their read-only part (`ledgerRO`) and their invariants (`slotsInv_alloc`)
  ihave ⟨#Hisls, Hslots⟩ : ([∗list] e ∈ slots, isSlot e.loc e.γ e.q) ∗
      ([∗list] e ∈ γl.slots, slotSt e.γ (SlotSt.init cf.blockLen) ∗
        slotPriv e.loc { phase := 0, round := 0, myProp := default, myBC := [] } ∗ queueFresh e.q)
    $$ [Hslots]
  · iapply BigSepL.bigSepL_sep_eqv.1
    iapply BigSepL.bigSepL_mono_of_forall ?_ $$ Hslots
    intro _ e
    unfold slotRes
    exact .rfl
  ihave #Hledro : ledgerRO γl ledger $$ []
  · unfold ledgerRO
    iframe #
    ipureintro; exact Hn2
  imod slotsInv_alloc γ cf hc k γl ⊤ $$ Hslots with ⟨%γc, #Hsinv, Hcres⟩
  -- server `k`'s keys, split
  unfold serverCore
  icases Hshare with ⟨#Hsh, Htokp, Htokn, Hkeys, Hbc⟩
  imod srvKeys_alloc γ k γl ⊤ $$ [Hkeys Hkp Hke] with ⟨#Hsk, Hkpp, Hkpe⟩
  · iframe
  wp_apply hProxy γ cf k γl γc ch id «$v1_ptr» ledger hid hk $$ [Htokp Hkpp Hcrp Hprc] as %p ⟨Hpok, #Hpro⟩
  · ihave Hprc := prc_of γl gprc rfl $$ Hprc
    isplitr; · iexact Hconf
    isplitr; · iexact Hchans
    isplitr; · iexact Hledro
    isplitr; · iexact Hsinv
    isplitr; · iexact Hsh
    unfold proxyBootRes
    isplitl [Hkpp]; · iexact Hkpp
    isplitr; · iexact Hsk
    isplitl [Hcrp]; · unfold crAuth; iexact Hcrp
    iexact Hprc
  wp_apply hNet γ cf k γl ch id «$v1_ptr» hid hk $$ [Htokn Hce2n Hpn2h Hhlog Hbc Hpush Hrcpt]
    as %nl Hnok
  · isplitr; · iexact Hconf
    isplitr; · iexact Hchans
    isplitr; · iexact Hsh
    unfold networkBootRes
    isplitl [Hce2n]; · iexact Hce2n
    isplitl [Hpn2h]; · iexact Hpn2h
    isplitl [Hhlog]; · unfold hAuth; iexact Hhlog
    isplitl [Hbc]; · iexact Hbc
    iapply BigSepL.bigSepL_sep_eqv.2
    isplitl [Hpush]
    · unfold pushAuth; iexact Hpush
    · unfold rcptAuth; iexact Hrcpt
  imod sync.init_WaitGroup (srvWgN k) «$v1_ptr» $$ «$v1» with ⟨%γw, #Hwg, Hwc, Hww⟩
  ipersist SvrId
  ipersist Done
  ipersist Proxy
  ipersist Network
  ipersist Wg
  wp_apply +noauto hCons γ cf k γl γc ch id «$v1_ptr» ledger hid hk $$ [Hcres Hcn2h Hpe2n Hexlog Hkpe]
    as %cl ⟨Hexr, Hhar, #Hstro⟩
  · isplitr; · iexact Hconf
    isplitr; · iexact Hchans
    isplitr; · iexact Hledro
    isplitr; · iexact Hsinv
    isplitl [Hcres]; · iexact Hcres
    unfold consensusBootRes
    isplitl [Hcn2h]; · iexact Hcn2h
    isplitl [Hpe2n]; · iexact Hpe2n
    isplitl [Hexlog]; · unfold exAuth; iexact Hexlog
    isplitl [Hkpe]; · iexact Hkpe
    iexact Hsk
  wp_pures
  wp_load
  wp_pures
  wp_store
  ipersist Consensus
  wp_auto
  have hidk : id = W32 (k : Int) := by subst hid; word
  subst hidk
  iapply HΦ
  unfold serverBuilt
  iexists γl, γc, ch, p, nl, cl, ledger
  isplitr
  · unfold serverRO; iframe #
  isplitl [Hwc Hww]
  · unfold serverOwn; iexists «$v1_ptr», γw; iframe; iframe #
  iframe #
  iframe

end proof
end Perennial.rabia.roles.server
