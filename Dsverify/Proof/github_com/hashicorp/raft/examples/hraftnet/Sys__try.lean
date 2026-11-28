/-
`hraftnet.Sys.try`'s proof (notes/dsv-hraft.md, S5f): an `Apply` with the operation's state as the
deposit (`apply_dep`), its answer claimed (`apply_done`) or the state back; a read outside the log by
`readCall.law`, proved from `Conn.Call.spec` (`readCall_law_holds`, `ReadCall.lean`, S6).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Sys__try
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn__Call
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.apiTimeout
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecApi
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ReadCall

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot rpctransport service


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : Net.NetProtoGS] [rsem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]
variable [rpcsem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [net.rpc.Assumptions] [net.Assumptions]


attribute [local instance] GooseGlobalGS.gooseInvGS

set_option goose.wp.extras true

theorem Sys.try.wp_proof
    (wp_Call : rpctransport.Conn.Call.spec (GF := GF) (hG := hG))
    (wp_apiTimeout : apiTimeout.spec (GF := GF)) :
    Sys.try.spec (GF := GF) (hG := hG) := by
  have wp_read := readCall_law_holds (GF := GF) (hG := hG) wp_Call
  intro K s sv j cmd d i Ψ hj1 hj6 hd hdl
  unfold sysConns cliEnv
  wp_start as ⟨⟨#Hpk, #Hpkr, %Hss, #Hdi, #Hcod⟩, Hs, ⟨%ps, #Hps, %Hpl, #Hcs⟩, #Hcmd, Hst, #Hru⟩
  wp_auto
  unfold inS
  rcases i with ⟨⟨put, way, v⟩, hok⟩
  simp only
  cases put
  · wp_auto
    wp_if_destruct
    · wp_alloc ap as Hap
      wp_auto
      wp_apply (lc := 2) wp_apiTimeout as %dd -
      ihave %Hlen := ownSlice_len _ _ _ $$ Hps
      obtain ⟨p, hp⟩ : ∃ p, ps[uint.nat j - 1]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hs : 0 ≤ sint.Z (j - W64 1) ∧ sint.Z (j - W64 1) < sint.Z sv.conns'.len := by
        have h1 := Hlen.1; rw [Hpl] at h1
        constructor <;> word
      rw [ite_eq_left hs]
      have hidx : (sint.Z (j - W64 1)).toNat = uint.nat j - 1 := by word
      wp_apply wp_load_slice_index sv.conns' (sint.Z (j - W64 1)) _ DfracDiscarded p hs.1 $$ [Hps] as -
      · iframe Hps; ipureintro; rw [hidx]; exact hp
      ihave #Hc := BigSepL.bigSepL_lookup hp $$ Hcs
      ipersist Hap
      wp_apply (wp_Call p K.W (serverAddrs.getD (uint.nat j - 1) go!"") go!"API.Apply" go!"API" go!"Apply"
          (apiSvcK K) (ptrI service.ApplyArgs.ty ap) (ptrI service.ApplyReply.ty «$r0_ptr»)
          (okAns (applyOk K d ⟨(false, W64 0, v), hok⟩ Ψ)) iprop(True)
          iprop(«$r0_ptr» ↦ (Perennial.zero_val service.ApplyReply))
          (fun _ _ => iprop(∃ (w : service.ApplyReply) (n k : Nat) (r : ApplyReplyV), «$r0_ptr» ↦ w ∗
            ⌜w.Status' = r.status ∧ w.Found' = r.found ∧ w.V' = r.v⌝ ∗ chosen K.γc n ∗
            frInv (K.γs n) (K.fcs n) ∗ applyOut (K.γs n) (K.fcs n) d k (applyRepOf r) ∗
            kitTicket K.g d ⟨(false, W64 0, v), hok⟩ Ψ))
          hraftCodec dd iprop(opSt K d ⟨(false, W64 0, v), hok⟩ Ψ ∗ £ 1 ∗ £ 1))
        $$ [$Hc $Hcod Hst Hlc1 Hlc2 «$r0»] as %r Hr
      · isplitr
        · ipureintro
          refine ⟨by decide, ?_, by simp [ptrI, interface.mkOk]⟩
          rw [Hss (uint.nat j) go!"API" hj1 hj6]
          simp [rpctransport.svcName]
        isplitr
        · ipureintro; decide
        isplitl [Hst Hlc1 Hlc2]
        · iframe Hst Hlc1 Hlc2
        isplitr
        · iintro ⟨Hst, Hl1, Hl2⟩
          iapply (enc_ApplyArgs ap DfracDiscarded (service.ApplyArgs.mk cmd) ⟨d⟩)
          iframe Hap
          isplitr
          · unfold applyArgsOwn; iexact Hcmd
          iintro - -
          isplitr
          · ipureintro; exact encApplyArgs_length ⟨d⟩ hdl
          isplitl
          · iapply apply_dep K ⟨d⟩ _ Ψ hd $$ [$Hdi $Hl1 $Hl2 $Hst]
          itrivial
        iframe «$r0»
        imodintro
        iintro HD %rep Hrep
        unfold okAns applyOk
        icases Hrep with (%Hne | ⟨%n, %k, %r, #Hcn, #Hfi, %Hrep, Hout, Htk⟩)
        · exfalso; exact Hne rfl
        subst Hrep
        iapply (dec_ApplyReply _ r)
        iframe HD
        iintro %w Hw Hown
        unfold applyReplyOwn
        icases Hown with %Hown
        iexists w, n, k, r
        iframe Hw Hcn Hfi Hout Htk
        ipureintro; exact Hown
      icases Hr with (⟨%Hr0, -, %rep, %w, %n, %k, %r, Hw, %Hown, #Hcn, #Hfi, Hout, Htk⟩ |
        ⟨%Hr1, ⟨Hst, -, -⟩, -⟩ | %Hr2)
      · subst Hr0
        wp_auto_lc 2
        obtain ⟨hst, hfd, hv⟩ := Hown
        wp_if_destruct
        · ihave Htok := applyOut_noEffect _ _ d k (applyRepOf r) (by rw [hst] at Hif; exact Hif) $$ Hout
          iapply HΦ
          iframe Hs
          simp only [Bool.false_eq_true, ↓reduceIte]
          unfold opSt
          iright
          iexists n, k
          iframe Hcn Hfi Htok Htk
        by_cases hs1 : r.status = W64 1
        · iapply fupd_wp
          imod apply_done K d ⟨(false, W64 0, v), hok⟩ Ψ n k r hs1 $$ [$Hlc1 $Hlc2 $Hfi $Hout $Htk]
            with ⟨%out, HΨ, %Ho⟩
          imodintro
          (try wp_auto)
          wp_if_destruct
          · iapply HΦ
            iframe Hs
            simp only [↓reduceIte]
            unfold outRes
            ileft
            iexists out
            iframe HΨ
            ipureintro
            simp only [Bool.false_eq_true, ↓reduceIte] at Ho
            rw [Ho, hfd, hv]
          · exfalso; exact Hif (hst ▸ hs1)
        · (try wp_auto)
          wp_if_destruct
          · exfalso; exact hs1 (hst ▸ Hif)
          · iapply HΦ
            iframe Hs
            simp only [↓reduceIte]
            unfold outRes
            iright; ipureintro; rfl
      · subst Hr1
        (try wp_auto)
        iapply HΦ
        iframe Hs
        simp only [Bool.false_eq_true, ↓reduceIte]
        iexact Hst
      · subst Hr2
        (try wp_auto)
        iapply HΦ
        iframe Hs
        simp only [↓reduceIte]
        unfold outRes
        iright; ipureintro; rfl

    · (try wp_auto)
      wp_alloc ap as Hap
      (try wp_auto)
      wp_apply (lc := 2) wp_apiTimeout as %dd -
      ihave %Hlen := ownSlice_len _ _ _ $$ Hps
      obtain ⟨p, hp⟩ : ∃ p, ps[uint.nat j - 1]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hs : 0 ≤ sint.Z (j - W64 1) ∧ sint.Z (j - W64 1) < sint.Z sv.conns'.len := by
        have h1 := Hlen.1; rw [Hpl] at h1
        constructor <;> word
      rw [ite_eq_left hs]
      have hidx : (sint.Z (j - W64 1)).toNat = uint.nat j - 1 := by word
      wp_apply wp_load_slice_index sv.conns' (sint.Z (j - W64 1)) _ DfracDiscarded p hs.1 $$ [Hps] as -
      · iframe Hps; ipureintro; rw [hidx]; exact hp
      ihave #Hc := BigSepL.bigSepL_lookup hp $$ Hcs
      unfold readUpd
      icases Hru with (%Hn | #Hlin)
      · exfalso; rcases Hn with h | h
        · cases h
        · exact Hif h
      wp_apply (wp_read K p (uint.nat j - 1) ⟨(false, way, v), hok⟩ Ψ ap «$r0_ptr» dd rfl Hif (by omega))
        $$ [$Hpkr $Hc $Hcod $Hdi $Hlc1 $Hlc2 $Hap $«$r0» $Hlin] as %r Hr
      · ipureintro; exact Hss
      icases Hr with (⟨%Hr0, %w, Hw, Hok⟩ | %Hr1 | %Hr2)
      · subst Hr0
        (try wp_auto)
        cases hok' : w.Ok'
        · simp only [Bool.not_false]
          (try wp_auto)
          iapply HΦ
          iframe Hs
          simp only [Bool.false_eq_true, ↓reduceIte]
          iexact Hst
        · simp only [Bool.not_true]
          ihave ⟨%out, %Ho, HΨ⟩ := Hok $$ %trivial
          (try wp_auto)
          iapply HΦ
          iframe Hs
          simp only [↓reduceIte]
          unfold outRes
          ileft
          iexists out
          iframe HΨ
          ipureintro
          rw [Ho]
      · subst Hr1
        (try wp_auto)
        iapply HΦ
        iframe Hs
        simp only [Bool.false_eq_true, ↓reduceIte]
        iexact Hst
      · subst Hr2
        (try wp_auto)
        iapply HΦ
        iframe Hs
        simp only [↓reduceIte]
        unfold outRes
        iright; ipureintro; rfl
  · wp_auto
    wp_alloc ap as Hap
    wp_auto
    wp_apply (lc := 2) wp_apiTimeout as %dd -
    ihave %Hlen := ownSlice_len _ _ _ $$ Hps
    obtain ⟨p, hp⟩ : ∃ p, ps[uint.nat j - 1]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hs : 0 ≤ sint.Z (j - W64 1) ∧ sint.Z (j - W64 1) < sint.Z sv.conns'.len := by
      have h1 := Hlen.1; rw [Hpl] at h1
      constructor <;> word
    rw [ite_eq_left hs]
    have hidx : (sint.Z (j - W64 1)).toNat = uint.nat j - 1 := by word
    wp_apply wp_load_slice_index sv.conns' (sint.Z (j - W64 1)) _ DfracDiscarded p hs.1 $$ [Hps] as -
    · iframe Hps; ipureintro; rw [hidx]; exact hp
    ihave #Hc := BigSepL.bigSepL_lookup hp $$ Hcs
    ipersist Hap
    wp_apply (wp_Call p K.W (serverAddrs.getD (uint.nat j - 1) go!"") go!"API.Apply" go!"API" go!"Apply"
        (apiSvcK K) (ptrI service.ApplyArgs.ty ap) (ptrI service.ApplyReply.ty «$r0_ptr»)
        (okAns (applyOk K d ⟨(true, way, v), hok⟩ Ψ)) iprop(True)
        iprop(«$r0_ptr» ↦ (Perennial.zero_val service.ApplyReply))
        (fun _ _ => iprop(∃ (w : service.ApplyReply) (n k : Nat) (r : ApplyReplyV), «$r0_ptr» ↦ w ∗
          ⌜w.Status' = r.status ∧ w.Found' = r.found ∧ w.V' = r.v⌝ ∗ chosen K.γc n ∗
          frInv (K.γs n) (K.fcs n) ∗ applyOut (K.γs n) (K.fcs n) d k (applyRepOf r) ∗
          kitTicket K.g d ⟨(true, way, v), hok⟩ Ψ))
        hraftCodec dd iprop(opSt K d ⟨(true, way, v), hok⟩ Ψ ∗ £ 1 ∗ £ 1))
      $$ [$Hc $Hcod Hst Hlc1 Hlc2 «$r0»] as %r Hr
    · isplitr
      · ipureintro
        refine ⟨by decide, ?_, by simp [ptrI, interface.mkOk]⟩
        rw [Hss (uint.nat j) go!"API" hj1 hj6]
        simp [rpctransport.svcName]
      isplitr
      · ipureintro; decide
      isplitl [Hst Hlc1 Hlc2]
      · iframe Hst Hlc1 Hlc2
      isplitr
      · iintro ⟨Hst, Hl1, Hl2⟩
        iapply (enc_ApplyArgs ap DfracDiscarded (service.ApplyArgs.mk cmd) ⟨d⟩)
        iframe Hap
        isplitr
        · unfold applyArgsOwn; iexact Hcmd
        iintro - -
        isplitr
        · ipureintro; exact encApplyArgs_length ⟨d⟩ hdl
        isplitl
        · iapply apply_dep K ⟨d⟩ _ Ψ hd $$ [$Hdi $Hl1 $Hl2 $Hst]
        itrivial
      iframe «$r0»
      imodintro
      iintro HD %rep Hrep
      unfold okAns applyOk
      icases Hrep with (%Hne | ⟨%n, %k, %r, #Hcn, #Hfi, %Hrep, Hout, Htk⟩)
      · exfalso; exact Hne rfl
      subst Hrep
      iapply (dec_ApplyReply _ r)
      iframe HD
      iintro %w Hw Hown
      unfold applyReplyOwn
      icases Hown with %Hown
      iexists w, n, k, r
      iframe Hw Hcn Hfi Hout Htk
      ipureintro; exact Hown
    icases Hr with (⟨%Hr0, -, %rep, %w, %n, %k, %r, Hw, %Hown, #Hcn, #Hfi, Hout, Htk⟩ |
      ⟨%Hr1, ⟨Hst, -, -⟩, -⟩ | %Hr2)
    · subst Hr0
      wp_auto_lc 2
      obtain ⟨hst, hfd, hv⟩ := Hown
      wp_if_destruct
      · ihave Htok := applyOut_noEffect _ _ d k (applyRepOf r) (by rw [hst] at Hif; exact Hif) $$ Hout
        iapply HΦ
        iframe Hs
        simp only [Bool.false_eq_true, ↓reduceIte]
        unfold opSt
        iright
        iexists n, k
        iframe Hcn Hfi Htok Htk
      by_cases hs1 : r.status = W64 1
      · iapply fupd_wp
        imod apply_done K d ⟨(true, way, v), hok⟩ Ψ n k r hs1 $$ [$Hlc1 $Hlc2 $Hfi $Hout $Htk]
          with ⟨%out, HΨ, %Ho⟩
        imodintro
        (try wp_auto)
        wp_if_destruct
        · iapply HΦ
          iframe Hs
          simp only [↓reduceIte]
          unfold outRes
          ileft
          iexists out
          iframe HΨ
          ipureintro
          simp only [↓reduceIte] at Ho
          rw [Ho]
          rfl
        · exfalso; exact Hif (hst ▸ hs1)
      · (try wp_auto)
        wp_if_destruct
        · exfalso; exact hs1 (hst ▸ Hif)
        · iapply HΦ
          iframe Hs
          simp only [↓reduceIte]
          unfold outRes
          iright; ipureintro; rfl
    · subst Hr1
      (try wp_auto)
      iapply HΦ
      iframe Hs
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexact Hst
    · subst Hr2
      (try wp_auto)
      iapply HΦ
      iframe Hs
      simp only [↓reduceIte]
      unfold outRes
      iright; ipureintro; rfl

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
