/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/bridge__serveListen.lean`. Each
iteration holds the loop's thread token, which the `Add` for the new `serveConn` deposits and the
`go` statement gives back fresh; the registration (under the mutex) splits the mutex's share of
`b.blackholec` in two, for the new connection's goroutines. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__serveListen
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__serveConn
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridgeConn__Close
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.dialer__Dial
public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridge

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.third_party

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

theorem bridge.serveListen.wp_proof (wp_serveConn : bridge.serveConn.spec (GF := GF) (hG := hG))
    (wp_Close : bridgeConn.Close.spec (GF := GF) (hG := hG))
    (wp_Dial : dialer.Dial.spec (GF := GF) (hG := hG)) :
    bridge.serveListen.spec (GF := GF) (hG := hG) := by
  intro b γ addr
  wp_start as ⟨#Hb, Hsl, Htok⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hbi := Hb
  iunfold isBridge at Hbi
  icases Hbi with ⟨%l, %sc, %γsc, #Hd, #Hl, #Hrl, #Hsc, #Hscb, #Hmu, #Hwg, #Hwgi, %Htb⟩
  wp_apply wp_with_defer as %defer defer
  ipersist b
  ihave HI : iprop("Htok" ∷ threadTok) $$ [Htok]
  · iframe
  wp_for HI
  wp_apply relay.Accept l addr $$ [] as %ci %ierr Hr
  · iframe #
  icases Hr with (⟨%Herr, %co, %Hci, #Hco, Hfresh⟩ | %Herr)
  · subst Herr Hci
    wp_auto
    wp_apply +noauto sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, Hi⟩
    · iframe #
    iunfold lockInv at Hi
    icases Hi with ⟨%m, %conns, %shares, %reg, %pc, %bhc, %γpc, %γbh, %holed, %q, Hconns, Hm, %Hdom,
      Hpausec, #Hpc, Hpcst, Hbh, #Hbhc, Hholed, Hbhst, Hwand, Hregs, Hreg, #Hregf, %Hsub⟩
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hconns Hm Hpausec Hpcst Hbh Hholed Hbhst Hwand
      Hregs Hreg]
    · iframe #
      iunfold lockInv
      iexists m, conns, shares, reg, pc, bhc, γpc, γbh, holed, q
      iframe
      iframe #
      ipureintro; exact ⟨Hdom, Hsub⟩
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γsc
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownBroadcastChan_is_chan $$ Hscb
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hscb
      iintro ⟨-, -⟩
      wp_auto
      wp_apply net.ConnClose co $$ [] as %_ -
      · iframe #
      wp_for_post
      wp_apply relay.ListenerClose l addr $$ [] as %_ -
      · iframe #
      wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, Hi⟩
      · iframe #
      iunfold lockInv at Hi
      icases Hi with ⟨%m, %conns, %shares, %reg, %pc, %bhc, %γpc, %γbh, %holed, %q, Hconns, Hm, %Hdom,
        Hpausec, #Hpc, Hpcst, Hbh, #Hbhc, Hholed, Hbhst, Hwand, Hregs, Hreg, #Hregf, %Hsub⟩
      icases regs_connOk b shares $$ Hregs with ⟨Hregs, #Hcs⟩
      wp_auto
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) (Val #m)) _)
      iapply (wp_close_all b m _ conns shares iprop(∃ v : Loc, bc_ptr ↦ v) _ Hdom) $$ [] [] [bc] Hm
      · iintro !> %c %q' %γt #Hc ⟨%v, Hbcp⟩
        wp_auto
        wp_apply wp_Close b c q' γt $$ [] as #-
        · iframe #
        isplitr
        · ipureintro; rfl
        iexists _; iexact Hbcp
      · iexact Hcs
      · iexists _; iexact bc
      iintro ⟨%v, bc⟩ Hm
      wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hconns Hm Hpausec Hpcst Hbh Hholed Hbhst Hwand
        Hregs Hreg]
      · iframe #
        iunfold lockInv
        iexists m, conns, shares, reg, pc, bhc, γpc, γbh, holed, q
        iframe
        iframe #
        ipureintro; exact ⟨Hdom, Hsub⟩
      wp_apply wp_bridgeWg_Done_sl b γ $$ [Hsl]
      · iframe #; iframe
      iapply HΦ
      iexact Htok
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, pc, γpc
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownBroadcastChan_is_chan $$ Hpc
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hpc
      iintro ⟨-, -⟩
      wp_auto
      wp_apply wp_Dial addr $$ [] as %oc %oerr Hr2
      icases Hr2 with (⟨%Herr2, %co2, %Hoc, #Hco2, Hdialed⟩ | %Herr2)
      · subst Herr2 Hoc
        wp_auto
        wp_apply chan.wp_make1 (V := Unit) as %dc %γd ⟨#Hdc, %-, Hdo⟩
        wp_apply wp_bridgeWg_Add b γ Htb $$ [Hsl Htok] as ⟨Hrun, Hsl⟩
        · iframe #; iframe
        wp_apply +noauto sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, Hi⟩
        · iframe #
        iunfold lockInv at Hi
        icases Hi with ⟨%m, %conns, %shares, %reg, %pc, %bhc, %γpc, %γbh, %holed, %q, Hconns, Hm,
          %Hdom, Hpausec, #Hpc', Hpcst, Hbh, #Hbhc', Hholed, Hbhst, Hwand, Hregs, Hreg, #Hregf',
          %Hsub⟩
        -- the new connection is not registered: its fields are owned whole
        iStructNamed «$r0»
        ihave Hfr : iprop(⌜reg !! «$r0_ptr» = none⌝ ∗ cF «$r0_ptr» go!"donec" ↦ dc) $$ [donec]
        · rcases hr : reg !! «$r0_ptr» with _ | x
          · iframe; ipureintro; rfl
          · ihave Hf := BigSepM.bigSepM_lookup (Φ := fun c (_ : Qp × GName) =>
              iprop(∃ (inc outc : GoInterfaceOk) (donec : GoChan),
                connFields (GF := GF) c inc outc donec)) hr $$ Hregf'
            icases Hf with ⟨%i', %o', %d', #Hf⟩
            iunfold connFields at Hf
            icases Hf with ⟨-, -, #Hd'⟩
            iexfalso
            iapply loc_own_discard (cF «$r0_ptr» go!"donec") dc d' $$ [donec]
            iframe
            iexact Hd'
        icases Hfr with ⟨%Hnreg, donec⟩
        wp_auto
        wp_apply (wp_mapInsert (go.GoType.PointerType bridge.bridgeConn.ty) m conns «$r0_ptr» ())
          $$ [$Hm] as Hm
        have hsh : shares.lookup «$r0_ptr» = none := by
          rcases h : shares.lookup «$r0_ptr» with _ | x
          · rfl
          · have := Hsub _ x h
            rw [show reg.lookup «$r0_ptr» = reg !! «$r0_ptr» from rfl, Hnreg] at this
            cases this
        ipersist in'
        ipersist out
        ipersist donec
        ihave #Hcf : connFields «$r0_ptr» co co2 dc $$ []
        · unfold connFields; iframe #
        imod token_alloc with ⟨%γt, Htk⟩
        icases share_out b bhc shares q «$r0_ptr» γt hsh $$ [Hbh Hwand] with ⟨Hbh, Hwand, Hshare⟩
        · iframe
        imod alloc_broadcast_chan (E := ⊤) (doneQ b q.half γt) γd dc $$ Hdc Hdo with Hdb
        icases ownBroadcastChan_Pending_Unknown _ _ _ $$ Hdb with ⟨Hdb, #Hdu⟩
        imod ghost_map_insert_persist «$r0_ptr» (q.half, γt) Hnreg $$ Hreg with ⟨Hreg, #Hrc⟩
        ihave Hp := relay.pair l co co2 addr $$ [Hfresh Hdialed]
        · iframe #; iframe
        imod Hp with ⟨Hd1, Hd2⟩
        ihave #Hcok : connOk b «$r0_ptr» q.half γt $$ []
        · unfold connOk; iexists co, co2, dc, γd; iframe #
        wp_apply wp_fork_tok_self $$ [Hrun Hdb Hshare Hd1 Hd2] as Htok
        · wp_apply wp_serveConn b γ addr «$r0_ptr» q.half γt l co co2 dc γd bhc γbh
            $$ [Hrun Hdb Hshare Hd1 Hd2] as Htok
          · iframe #; iframe
          iframe Htok
          ipureintro; exact isPanic_intoVal _
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hconns Hm Hpausec Hpcst Hbh Hholed Hbhst Hwand
          Hregs Hreg Htk]
        · iframe #
          iunfold lockInv
          iexists m, conns.insert «$r0_ptr» (), shares.insert «$r0_ptr» (q.half, γt),
            reg.insert «$r0_ptr» (q.half, γt), pc, bhc, γpc, γbh, holed, q.half
          iframe
          iframe #
          inext
          isplitr
          · ipureintro
            intro c'
            by_cases hc : c' = «$r0_ptr»
            · subst hc; rw [GMap.lookup_insert, GMap.lookup_insert]; rfl
            · rw [GMap.lookup_insert_ne _ _ (Ne.symm hc), GMap.lookup_insert_ne _ _ (Ne.symm hc)]
              exact Hdom c'
          isplitl [Hregs Htk]
          · iapply (BigSepM.bigSepM_insert (Φ := fun c (x : Qp × GName) =>
              iprop(connOk (GF := GF) b c x.1 x.2 ∗ token x.2)) hsh).2
            iframe
            iframe #
          isplitr
          · iapply (BigSepM.bigSepM_insert (Φ := fun c (_ : Qp × GName) =>
              iprop(∃ (inc outc : GoInterfaceOk) (donec : GoChan),
                connFields (GF := GF) c inc outc donec)) Hnreg).2
            iframe #
          ipureintro
          intro c' x h
          by_cases hc : c' = «$r0_ptr»
          · subst hc
            rw [GMap.lookup_insert] at h ⊢
            exact h
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm hc)] at h ⊢
            exact Hsub c' x h
        wp_for_post
        iframe
      · cases oerr with
        | nil => exact absurd rfl Herr2
        | ok ei =>
          wp_auto
          wp_apply net.ConnClose co $$ [] as %_ -
          · iframe #
          wp_for_post
          wp_apply relay.ListenerClose l addr $$ [] as %_ -
          · iframe #
          wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, Hi⟩
          · iframe #
          iunfold lockInv at Hi
          icases Hi with ⟨%m, %conns, %shares, %reg, %pc, %bhc, %γpc, %γbh, %holed, %q, Hconns, Hm, %Hdom,
            Hpausec, #Hpc, Hpcst, Hbh, #Hbhc, Hholed, Hbhst, Hwand, Hregs, Hreg, #Hregf, %Hsub⟩
          icases regs_connOk b shares $$ Hregs with ⟨Hregs, #Hcs⟩
          wp_auto
          wp_func_lits
          wp_bind (App (App (Val (map.forRange _ _)) (Val #m)) _)
          iapply (wp_close_all b m _ conns shares iprop(∃ v : Loc, bc_ptr ↦ v) _ Hdom) $$ [] [] [bc] Hm
          · iintro !> %c %q' %γt #Hc ⟨%v, Hbcp⟩
            wp_auto
            wp_apply wp_Close b c q' γt $$ [] as #-
            · iframe #
            isplitr
            · ipureintro; rfl
            iexists _; iexact Hbcp
          · iexact Hcs
          · iexists _; iexact bc
          iintro ⟨%v, bc⟩ Hm
          wp_auto
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hconns Hm Hpausec Hpcst Hbh Hholed Hbhst Hwand
            Hregs Hreg]
          · iframe #
            iunfold lockInv
            iexists m, conns, shares, reg, pc, bhc, γpc, γbh, holed, q
            iframe
            iframe #
            ipureintro; exact ⟨Hdom, Hsub⟩
          wp_apply wp_bridgeWg_Done_sl b γ $$ [Hsl]
          · iframe #; iframe
          iapply HΦ
          iexact Htok
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · cases ierr with
    | nil => exact absurd rfl Herr
    | ok ei =>
      wp_auto
      wp_for_post
      wp_apply relay.ListenerClose l addr $$ [] as %_ -
      · iframe #
      wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, Hi⟩
      · iframe #
      iunfold lockInv at Hi
      icases Hi with ⟨%m, %conns, %shares, %reg, %pc, %bhc, %γpc, %γbh, %holed, %q, Hconns, Hm, %Hdom,
        Hpausec, #Hpc, Hpcst, Hbh, #Hbhc, Hholed, Hbhst, Hwand, Hregs, Hreg, #Hregf, %Hsub⟩
      icases regs_connOk b shares $$ Hregs with ⟨Hregs, #Hcs⟩
      wp_auto
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) (Val #m)) _)
      iapply (wp_close_all b m _ conns shares iprop(∃ v : Loc, bc_ptr ↦ v) _ Hdom) $$ [] [] [bc] Hm
      · iintro !> %c %q' %γt #Hc ⟨%v, Hbcp⟩
        wp_auto
        wp_apply wp_Close b c q' γt $$ [] as #-
        · iframe #
        isplitr
        · ipureintro; rfl
        iexists _; iexact Hbcp
      · iexact Hcs
      · iexists _; iexact bc
      iintro ⟨%v, bc⟩ Hm
      wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hconns Hm Hpausec Hpcst Hbh Hholed Hbhst Hwand
        Hregs Hreg]
      · iframe #
        iunfold lockInv
        iexists m, conns, shares, reg, pc, bhc, γpc, γbh, holed, q
        iframe
        iframe #
        ipureintro; exact ⟨Hdom, Hsub⟩
      wp_apply wp_bridgeWg_Done_sl b γ $$ [Hsl]
      · iframe #; iframe
      iapply HΦ
      iexact Htok
end proof

end bridge
end EtcdGrove
end Perennial
