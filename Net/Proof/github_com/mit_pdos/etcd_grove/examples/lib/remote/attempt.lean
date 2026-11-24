/-
The proof of `attempt` (`Net/Spec/.../lib/remote/attempt.lean`): `DialTimeout` with the update
`dial_au` (a new connection's dialer end, `connEnd cn false (reqP S) (repP S) [] []`, and its
`connFresh`), the slot registered with the caller's update (`slot_register`), the deadline set
(`deadline_au`, its result ignored), the request's frame written (`writeFrame`, under `reqP`'s fact
for this slot), the reply's frame read (`readFrame`); a whole reply is, after a later credit strips
`recvTokL`'s later, a frame `repP` allows (`recvTok_proto`, `rep_read`): an answer to `i` that is not an output, or an
output `o` the slot recorded, whose `Φ o` the dialer takes with its token (`slot_take`, a second
credit). The close's result is ignored (`close_au`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.attempt
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.deadline
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.writeFrame
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.readFrame
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pkg
public import Net.Spec.net.DialTimeout
public import Net.Spec.net.Conn__SetDeadline
public import Net.Spec.net.Conn__Close

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {I O : Type} [Pos.Countable I] [Pos.Countable O]

theorem attempt.wp_proof (wp_DialTimeout : net.DialTimeout.spec (GF := GF) (hG := hG))
    (wp_SetDeadline : net.Conn.SetDeadline.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_deadline : deadline.spec (GF := GF) (hG := hG))
    (wp_writeFrame : writeFrame.spec (GF := GF) (hG := hG))
    (wp_readFrame : readFrame.spec (GF := GF) (hG := hG)) :
    attempt.spec (GF := GF) (hG := hG) (I := I) (O := O) := by
  intro S a i Φo req dq d Hlen
  wp_start as ⟨#Hm, #Ha, Hreq, HL, Hu⟩
  ihave ⟨%et, #Het⟩ := et_init $$ Hpkg
  ihave ⟨%ed, #Hed⟩ := ed_init $$ Hpkg
  ihave ⟨%eof, #Heof⟩ := eof_init $$ Hpkg
  ihave %Hok := addrTok_ok a $$ [Ha]
  · unfold svcAddr; iapply addrProto_tok $$ Ha
  wp_auto_lc 2
  wp_apply wp_DialTimeout go!"tcp" net.tcpNet_tcp a d et ed iprop(True)
      (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (reqP S a) (repP S) [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn false ∗
        rdlTok (Gg := hG.goose_globalGS) cn false false)) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, ⟨Hend, Hfresh, Hrdl⟩⟩ | ⟨-, %x, %e, -, #Herr, -⟩)
  · iframe Het Hed
    isplitr
    · ipureintro; exact Hok
    isplit
    · itrivial
    · unfold svcAddr
      iapply dial_rdl_au a (reqP S a) (repP S) $$ Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    wp_auto
    iapply fupd_wp
    imod slot_register S ⊤ (fun _ _ => CoPset.mem_full) a cn i Φo $$ Hm Hfresh HL Hu
      with ⟨%γ, #Hso, #Hsi, Htk⟩
    imodintro
    unfold connEnd
    icases Hend with ⟨Hsend, Hrecv⟩
    ihave #Hconn := sendTok_connIs cn false (reqP S a) [] $$ Hsend
    wp_apply wp_deadline as %tm -
    wp_apply wp_SetDeadline t cn false a la ra tm (fun _ => iprop(True)) $$ [Hrdl] as %err' -
    · iframe Hca
      imod deadline_au cn false (W64 0) _ false $$ Hrdl with ⟨%st, Hst, Hcl⟩
      imodintro
      iexists st
      iframe Hst
      iintro %res %st' %Hd Hst
      imod Hcl $$ %res %st' %Hd Hst with -
      imodintro
      itrivial
    ihave #Hc : net.isConn (GF := GF) (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn
        false a $$ []
    · unfold net.isConn
      iexists t, la, ra
      iframe Hca
      ipureintro; rfl
    wp_apply wp_writeFrame _ cn false a (reqP S a) [] req (S.encIn i) dq ed Hlen $$ [Hreq Hsend]
      as %ok ⟨%w, Hreq, -, -⟩
    · iframe Hc Hreq Hsend Hed
      imodintro
      unfold reqP
      iexists γ, i, Φo
      iframe Hso Hsi
      ipureintro; rfl
    cases ok
    · wp_auto
      wp_apply wp_Close t cn false a la ra (fun _ => iprop(True)) $$ [] as %err'' -
      · iframe Hca
        imod close_au cn false $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
        imodintro
        iexists st, dd
        iframe Hst Hdd
        iintro %res %st' %d' %Hd Hst Hdd
        imod Hcl $$ %res %st' %d' %Hd Hst Hdd with -
        imodintro
        itrivial
      iapply HΦ
      iframe Hreq
      ileft
      itrivial
    wp_auto
    ihave HrL := recvTok_L cn false (repP S) [] $$ Hrecv
    wp_apply wp_readFrame _ cn false a (repP S) [] eof ed $$ [HrL] as %b %ok ⟨%got, HrL, Hres⟩
    · iframe Hc Heof Hed HrL
    icases Hres with (%Hf | ⟨%bd, %Hbd, Hb⟩)
    · wp_apply wp_Close t cn false a la ra (fun _ => iprop(True)) $$ [] as %err'' -
      · iframe Hca
        imod close_au cn false $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
        imodintro
        iexists st, dd
        iframe Hst Hdd
        iintro %res %st' %d' %Hd Hst Hdd
        imod Hcl $$ %res %st' %d' %Hd Hst Hdd with -
        imodintro
        itrivial
      iapply HΦ
      iframe Hreq
      ileft
      ipureintro; exact Hf
    obtain ⟨rfl, rfl, Hbl⟩ := Hbd
    ihave HrL := recvTokL_later cn false (repP S) _ $$ HrL
    iapply fupd_wp
    imod (lc_fupd_elim_later (GF := GF) (E := ⊤) (P := recvTok (Gg := hG.goose_globalGS) cn false (repP S) ([] ++ frame bd))) $$ Hlc1 HrL with HrT
    icases recvTok_proto cn false (repP S) _ $$ HrT with ⟨-, #Hpp⟩
    rw [List.nil_append]
    icases rep_read S cn γ i bd (by simp only [maxLen] at Hbl; omega) $$ Hso Hpp with ⟨%v, %Hv, Hvk⟩
    subst Hv
    ihave HΦv : iprop(|={⊤}=> ((∃ o, ⌜v = S.ov o⌝ ∗ Φo o) ∨ ⌜S.unkAns i v⌝)) $$ [Hvk Htk Hlc2]
    · icases Hvk with (%Hu | ⟨%o, %Ho, #Hlb⟩)
      · imodintro
        iright
        ipureintro; exact Hu
      · imod slot_take S ⊤ (fun _ _ => CoPset.mem_full) a γ i Φo o $$ Hsi Htk Hlb Hlc2 with HΦo
        imodintro
        ileft
        iexists o
        iframe HΦo
        ipureintro; exact Ho
    imod HΦv
    imodintro
    wp_apply wp_Close t cn false a la ra (fun _ => iprop(True)) $$ [] as %err'' -
    · iframe Hca
      imod close_au cn false $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
      imodintro
      iexists st, dd
      iframe Hst Hdd
      iintro %res %st' %d' %Hd Hst Hdd
      imod Hcl $$ %res %st' %d' %Hd Hst Hdd with -
      imodintro
      itrivial
    iapply HΦ
    iframe Hreq
    iright
    iexists v
    iframe Hb HΦv
    ipureintro; rfl
  · icases net.opErr_netErr _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne
    wp_auto
    iapply HΦ
    iframe Hreq
    ileft
    itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
