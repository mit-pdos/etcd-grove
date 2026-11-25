/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/OrchSend.lean (lab master
915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md), onto `Net/`'s `Dial`, `Write`, `Read`,
`Close` (`SwNetDeps`; dsv-rabia's `sendConf.wp_proof` shape).

`sendConf(a, b)` (`kit.go`), for the orchestrator: on a fresh connection to `a` it writes the
message `bs` (meeting `a`'s dialer protocol `P`), reads one byte back and closes the connection;
`true` only if the byte is `confAck`, and then the acceptor's protocol `Q` held of a reply that
starts with `confAck` (for a predicted node's configuration port, `conf.ackQP`: its prediction is
registered).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitDeps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [examples.swiftnet.Assumptions]
variable [net.Assumptions] [io.Assumptions]

set_option goose.wp.extras true in
theorem sendConf.wp_proof (D : SwNetDeps (hG := hG)) : sendConf.spec (hG := hG) := by
  intro a b bs P Q
  wp_start as ⟨#Hproto, #HP, Hb⟩
  ihave %Haok := addrTok_ok a $$ [Hproto]
  · iapply addrProto_tok $$ Hproto
  ihave ⟨%ed, #Hed⟩ := kit_ed_init $$ Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp netDistGF) pkg_id.io) $$ []
  · iPkgInit
  wp_auto
  ihave #HnetPk : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · solve_pkg_init
  wp_apply D.dial go!"tcp" net.tcpNet_tcp a iprop(True)
      (fun cid => iprop(connEnd (Gg := hG.goose_globalGS) cid false P Q [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cid false)) $$ []
    as %cv %err (⟨%Herr, %cid, #Hcl, ⟨Hend, -⟩⟩ | ⟨-, %x, -, #Herr⟩)
  · (try iframe HnetPk)
    isplitr
    · ipureintro; exact Haok
    isplit
    · itrivial
    · iapply dial_au a P Q $$ Hproto
  · subst Herr
    wp_auto
    iunfold connEnd at Hend
    icases Hend with ⟨Hsend, Hrecv⟩
    ihave #Hconn := sendTok_connIs cid false _ _ $$ Hsend
    unfold net.isConn
    icases Hcl with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    wp_auto
    ihave #HP' : □ P cid ([] ++ bs) $$ []
    · imodintro; rw [List.nil_append]; iapply HP
    wp_apply D.write t cid false a la ra b bs (DFrac.own 1) ed
        (writeP cid false P []) $$ [Hb Hsend]
      as %nw %err ⟨%w, %res, Hsend, Hb, %Hw, #HE⟩
    · iframe Hca Hb Hed
      isplitl [Hsend]
      · iapply writeP_init $$ Hsend
      · iapply write_acc cid false P [] bs $$ HP'
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    cases res with
    | some k =>
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_apply wp_closeConn D t cid false a la ra $$ [] as %_ -
      · iframe #
      try wp_auto
      iapply HΦ; try simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    | none =>
      have herr := Hne.1 rfl
      subst herr
      wp_auto_lc 1
      ihave Hsl := slice_array (V := w8) a_ptr 1 _ (by decide) $$ a
      ihave HRL := recvTok_L cid false Q [] $$ Hrecv
      try wp_auto
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
        show (W64 1 - W64 0 : w64) = W64 1 from rfl]
      wp_apply rabia.examples.rabianet.wp_connReadFull D.read D.readFullLt t cid false a la ra ed
          Q [] _ _ $$ [$Hio $Hca $Hed $HRL $Hsl]
        as %n %err ⟨%data, %Hd, Hsl, Hrecv⟩
      obtain ⟨-, hdl, herr⟩ := Hd
      have hz : (zero_val (GoArray w8 1)).arr.length = 1 := rfl
      rw [hz] at hdl herr
      rcases err with e | _
      · dsimp only
        wp_auto
        wp_apply wp_closeConn D t cid false a la ra $$ [] as %_ -
        · iframe #
        try wp_auto
        iapply HΦ; try simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      have hl1 : data.length = 1 := herr rfl
      obtain ⟨x, rfl⟩ : ∃ x, data = [x] := by
        rcases data with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> simp at hl1; exact ⟨x, rfl⟩
      ihave ⟨Hrecv, Hp⟩ := recvTokL_proto _ _ _ _ $$ Hrecv
      iapply fupd_wp
      imod (lc_fupd_elim_later (GF := netDistGF) (E := ⊤)) $$ Hlc1 Hp with #Hp
      imodintro
      rw [show [x] ++ List.drop [x].length (List.replicate 1 (zero_val w8)) = [x] from rfl]
      icases (ownSlice_elem_acc (V := w8) 0 x _ _ [x] (by decide) rfl) $$ Hsl with ⟨Hx, -⟩
      wp_auto
      ihave Hx : arrayIndexRef w8 (sint.Z (W64 0)) a_ptr ↦ x $$ [Hx]
      · rw [show sint.Z (W64 0) = (0 : Int) from rfl]; unfold sliceIndexRef; iexact Hx
      wp_auto
      wp_if_destruct
      · wp_apply wp_closeConn D t cid false a la ra $$ [] as %_ -
        · iframe #
        try wp_auto
        iapply HΦ
        simp only [↓reduceIte]
        unfold protoPrefix
        icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
        · simp at Hnil
        iexists cid, ext
        iframe HQ
        ipureintro
        simpa [confAck] using Hext
      all_goals
        wp_apply wp_closeConn D t cid false a la ra $$ [] as %_ -
        · iframe #
        try wp_auto
        iapply HΦ; try simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · rcases err with e | _
    · wp_auto
      iapply HΦ; try simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
      exact absurd (Hne.2 (by simp)) (by intro h; obtain ⟨_, h⟩ := h; cases h)

end proof

end Perennial.github_com.imdea_software.swiftpaxos
