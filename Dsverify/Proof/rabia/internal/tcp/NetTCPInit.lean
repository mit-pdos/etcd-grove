/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/NetTCPInit.lean`, run
`rabia-r1wake-1`, onto `Net/`'s `Listen` (`net.Listen.wp_proof` with `listen_au` at the address's
protocols, `shared_netProto`).)

The proof of `rabia/internal/tcp.NetTCPInit`: the listen retry loop, the receive channel (an
ordered channel of `n` producers).
-/
module

public import Dsverify.Proof.rabia.internal.tcp.Basics
public import Net.Proof.net.Listen
public import Net.Proof.net.AtAddr

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message rabia.internal.config

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.internal.tcp.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]

set_option goose.wp.extras true

theorem NetTCPInit.wp_proof : NetTCPInit.spec (GF := GF) := by
  intro γ cf k γl id hid hk
  wp_start as ⟨#Hconf, #Hsh⟩
  ihave #Hconf0 := Hconf
  unfold confRO
  icases Hconf with ⟨%hok, %ps, #Hconf, #Hps⟩
  have hn : cf.n ≤ maxS := by unfold maxS; unfold RCfg.Ok at hok; omega
  have hkm : k < maxS := by omega
  ihave #Hproto := shared_netProto γ k hkm $$ Hsh
  ihave %Haok := addrTok_ok (netAddr k) $$ [Hproto]
  · iapply addrProto_tok $$ Hproto
  ihave Hc2 := Hconf
  iStructNamed Hc2
  wp_auto
  wp_apply (net.Listen.spec_addrOk net.Listen.wp_proof) go!"tcp" net.tcpNet_tcp (netAddr k) as %lv %err Hres
  · iframe %Haok
    iapply listen_au $$ Hproto
  ihave HI : (∃ (lv err : GoInterface), "listener" ∷ listener_ptr ↦ lv ∗ "err" ∷ err_ptr ↦ err ∗
      "Hres" ∷ ((⌜err = interface.nil⌝ ∗ ∃ (l : w64), ownListener lv l (netAddr k)) ∨
        (∃ i, ⌜err = interface.ok i⌝)) :
      IProp GF) $$ [listener err Hres]
  · iexists lv, err
    iframe
    icases Hres with (⟨%He, %l, #Hl, Hlis, #Hla⟩ | ⟨%x, -, #HE⟩)
    · ileft; iframe %He; iexists l; unfold ownListener; iframe Hl Hlis Hla
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      iright; iexists _; ipureintro; rfl
  wp_for HI
  icases Hres with (⟨%He, %l, Hl⟩ | ⟨%i, %Heq⟩)
  · subst He
    wp_auto
    cleanup_bool_decide
    wp_auto
    ihave %Hpl := ownSlice_len _ _ _ $$ Hps
    have hps : ps.len = W64 cf.n := by
      have h1 := Hpl.1; simp only [peerStrs, List.length_map, List.length_range] at h1
      unfold maxS at hn; word
    simp only [hps, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply (chan.wp_make1 (V := Unit)) as %done %γd ⟨#Hdone, -, Hdo⟩
    imod start_bag (doneP (GF := GF)) .Idle done γd (by simp) $$ Hdone Hdo with #Hdb
    imod wg_alloc «$v1_ptr» (2 * cf.n) (by unfold maxS at hn; unfold wgMax; omega) $$ «$v1» with Hwg
    wp_apply (chan.wp_make2 (V := Msg) (W64 500000)) as %rc %γrc ⟨#Hrc, -, Hrco⟩
    · ipureintro; decide
    imod start_ord rc cf.n (recvP (GF := GF) γ cf k γl) γrc $$ Hrc [Hrco] with ⟨%γr, %Hγr, #Hord, Hcons, Hprods⟩
    · iright; iexact Hrco
    have hz : 0 ≤ sint.Z (W64 cf.n) := by unfold maxS at hn; word
    have hzn : sint.nat (W64 cf.n) = cf.n := by unfold maxS at hn; word
    wp_apply (wp_slice_make2 (V := GoChan) _) as %scs ⟨Hscs, -⟩
    · ipureintro; exact hz
    wp_apply (wp_slice_make2 (V := Loc) _) as %rcs ⟨Hrcs, -⟩
    · ipureintro; exact hz
    wp_apply (wp_slice_make2 (V := Loc) _) as %sns ⟨Hsns, -⟩
    · ipureintro; exact hz
    wp_apply (wp_slice_make2 (V := Loc) _) as %rds ⟨Hrds, -⟩
    · ipureintro; exact hz
    wp_apply +noauto (wp_slice_make2 (V := Loc) _) as %wrs ⟨Hwrs, -⟩
    · ipureintro; exact hz
    ihave Hrcs := (show (rcs ↦* List.replicate (sint.nat (W64 cf.n)) (zero_val Loc) : IProp GF) ⊢
      rcs ↦* List.replicate cf.n (zero_val Loc) by rw [hzn]) $$ Hrcs
    wp_pures
    wp_alloc t as Ht
    iStructNamed Ht
    ipersist Id
    ipersist Listener
    ipersist Done
    ipersist Wg
    ipersist SendChan
    ipersist RecvChan
    ipersist RecvConn
    ipersist SendConn
    ipersist Readers
    ipersist Writers
    wp_auto
    iapply HΦ
    iexists γr
    iframe Hcons
    isplitr
    · unfold netTcpRecv
      iexists rc
      iframe #
    unfold netTcpOwn doneChan
    iexists lv, l, done, «$v1_ptr», scs, rcs, sns, rds, wrs, _, _, _, _
    iframe
    rw [← hid, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    iframe #
    isplitr
    · ipureintro; exact hid ▸ hk
    iframe #
    ipureintro; simpa using hzn
  · subst Heq
    wp_auto
    rw [if_pos (by simp)]
    wp_auto
    wp_apply time.wp_Sleep
    wp_apply (net.Listen.spec_addrOk net.Listen.wp_proof) go!"tcp" net.tcpNet_tcp (netAddr k) as %lv' %err' Hres
    · iframe %Haok
      iapply listen_au $$ Hproto
    wp_for_post
    iframe
    iexists lv', err'
    iframe
    icases Hres with (⟨%He, %l, #Hl, Hlis, #Hla⟩ | ⟨%x, -, #HE⟩)
    · ileft; iframe %He; iexists l; unfold ownListener; iframe Hl Hlis Hla
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      iright; iexists _; ipureintro; rfl

end proof

end Perennial.rabia.internal.tcp
