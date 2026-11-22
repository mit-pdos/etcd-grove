/-
The proof of `serveConn` (`Net/Spec/.../lib/remote/serveConn.lean`) on the acceptor's end of `cn`:
`SetDeadline` (`deadline_au`, its result ignored), `readFrame` (with the reader's `recvTokL`,
`recvTok_L`); on a frame `bd` read whole, its protocol fact (`recvTokL_later` and a later
credit, `recvTok_proto`) is the slot's input's (`req_read`: `bd = encIn i`), so `DecIn` returns
`iv i` if anything. Then the slot's claim (`slot_claim`: the acceptor's fresh token and a credit)
gives the update `S.upd i Φ`, which `op` takes (`svcOp`); an answered output `o` with `Φ o` is
recorded in the slot (`slot_done`, a credit), so its reply, as the unknown output's, meets the
acceptor's protocol `repP`: `EncOut`, then, if the encoding is at most `MaxLen` bytes,
`SetDeadline` and `writeFrame` with the acceptor's `sendTok`. Last, `Close` (`close_au`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.serveConn
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.deadline
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.readFrame
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.writeFrame
public import Net.Spec.net.Conn__SetDeadline
public import Net.Spec.net.Conn__Close
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pkg

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
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {I O : Type} [Pos.Countable I] [Pos.Countable O]

theorem serveConn.wp_proof
    (wp_deadline : deadline.spec (GF := GF) (hG := hG))
    (wp_SetDeadline : net.Conn.SetDeadline.spec (GF := GF) (hG := hG))
    (wp_readFrame : readFrame.spec (GF := GF) (hG := hG))
    (wp_writeFrame : writeFrame.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    serveConn.spec (GF := GF) (hG := hG) (I := I) (O := O) := by
  intro S c cn a sys op cd d tok
  wp_start as ⟨#Hc, Hend, Hfresh, #Hcd, #Hop, Htok⟩
  icases eof_init $$ Hpkg with ⟨%eof, #Heof⟩
  icases ed_init $$ Hpkg with ⟨%ed, #Hed⟩
  iunfold connEnd at Hend
  icases Hend with ⟨Hsend, Hrecv⟩
  ihave #Hci := sendTok_connIs $$ Hsend
  iunfold wireOk at Hcd
  icases Hcd with ⟨-, #HDecIn, #HEncOut, -⟩
  ihave #Hc' := Hc
  iunfold net.isConn at Hc'
  icases Hc' with ⟨%t, %la, %ra, %Hct, #Hca⟩
  subst Hct
  wp_auto
  wp_apply wp_deadline as %tm -
  wp_apply wp_SetDeadline t cn true a la ra tm (fun _ => iprop(True)) as %err -
  · iframe Hca
    imod deadline_au cn true _ _ $$ Hci with ⟨%st, Hst, Hk⟩
    imodintro
    iexists st
    iframe Hst
    iintro %res %st' %Hdo Hst'
    imod Hk $$ %res %st' %Hdo Hst' with -
    imodintro
    itrivial
  ihave Hrecv := recvTok_L $$ Hrecv
  wp_apply (lc := 3) wp_readFrame _ cn true a (reqP S) [] eof ed $$ [Hrecv]
    as %b %ok ⟨%got, Hrecv, Hres⟩
  · iframe Hc Heof Hed Hrecv
  icases Hres with (%Hok | ⟨%bd, %Hbd, Hb⟩)
  · -- the read failed: close
    subst Hok
    wp_auto
    wp_apply wp_Close t cn true a la ra (fun _ => iprop(True)) as %err' -
    · iframe Hca
      imod close_au cn true $$ Hci with ⟨%st, %dd, Hst, Hd, Hk⟩
      imodintro
      iexists st, dd
      iframe Hst Hd
      iintro %res %st' %d' %Hco Hst' Hd'
      imod Hk $$ %res %st' %d' %Hco Hst' Hd' with -
      imodintro
      itrivial
    iapply HΦ
    iexact Htok
  obtain ⟨rfl, rfl, Hbl⟩ := Hbd
  -- the request: the frame of the input of the connection's slot
  ihave Hrecv := recvTokL_later $$ Hrecv
  imod (lc_fupd_elim_later (GF := GF) (E := ⊤)
    (P := recvTok (Gg := hG.goose_globalGS) cn true (reqP (Gg := hG.goose_globalGS) S)
      ([] ++ frame bd))) $$ Hlc1 Hrecv with Hrecv
  icases recvTok_proto $$ Hrecv with ⟨-, #Hpp⟩
  rw [List.nil_append]
  have hbd : bd.length < 2 ^ 63 := by
    have : bd.length ≤ 2 ^ 20 := Hbl
    omega
  icases req_read S cn bd hbd $$ Hpp with ⟨%γ, %i, %Ψ, %Hbi, #Hso, #Hsi⟩
  subst Hbi
  wp_auto
  wp_apply HDecIn $$ %i %b %(DFrac.own 1) [Hb] as %x %good %Hx
  · iexact Hb
  cases good
  · -- it does not decode: close
    wp_auto
    wp_apply wp_Close t cn true a la ra (fun _ => iprop(True)) as %err' -
    · iframe Hca
      imod close_au cn true $$ Hci with ⟨%st, %dd, Hst, Hd, Hk⟩
      imodintro
      iexists st, dd
      iframe Hst Hd
      iintro %res %st' %d' %Hco Hst' Hd'
      imod Hk $$ %res %st' %d' %Hco Hst' Hd' with -
      imodintro
      itrivial
    iapply HΦ
    iexact Htok
  obtain rfl := Hx rfl
  -- claim the slot's update, and run `op` with it
  -- (the laws' updates are over the global ghost state's invariants, those of `hG` up to unfolding)
  ihave Hcl : (|={⊤}=> S.upd i Ψ ∗
      runTok (Gg := hG.goose_globalGS) (O := O) γ : IProp GF) $$ [Hfresh Hlc2]
  · iapply slot_claim S ⊤ CoPset.subseteq_top γ i Ψ $$ Hsi Hfresh Hlc2
  imod Hcl with ⟨Hlin, Hrun⟩
  iunfold svcOp at Hop
  wp_auto
  wp_apply Hop $$ %sys %i %Ψ [Htok Hlin] as %v ⟨Htok, Hv⟩
  · iframe Htok Hlin
  -- the reply: an output the slot records (`slot_done`), or the input's unknown output
  ihave Hr : (|={⊤}=> □ repP (Gg := hG.goose_globalGS) S cn ([] ++ frame (S.encOut v)) ∗
      ⌜S.outOk v⌝ : IProp GF) $$ [Hv Hrun Hlc3]
  · icases Hv with (⟨%o, %Hvo, HΨ⟩ | %Hvu)
    · ihave Hd : (|={⊤}=> doneLb (Gg := hG.goose_globalGS) γ o : IProp GF) $$ [Hrun HΨ Hlc3]
      · iapply slot_done S ⊤ CoPset.subseteq_top γ i Ψ o $$ Hsi Hrun HΨ Hlc3
      imod Hd with #Hdone
      imodintro
      isplit
      · imodintro
        iunfold repP
        iexists γ, i, v
        iframe Hso
        isplit
        · ipureintro; rfl
        · iright
          iexists o
          iframe Hdone
          ipureintro; exact Hvo
      · ipureintro; exact Or.inl ⟨o, Hvo⟩
    · imodintro
      isplit
      · imodintro
        iunfold repP
        iexists γ, i, v
        iframe Hso
        isplit
        · ipureintro; rfl
        · ileft
          ipureintro; exact Hvu
      · ipureintro; exact Or.inr ⟨i, Hvu⟩
  imod Hr with ⟨#Hrep, %Hout⟩
  wp_apply HEncOut $$ %v [] as %rep Hrepb
  · ipureintro; exact Hout
  ihave %Hlen := ownSlice_len $$ Hrepb
  wp_if_destruct
  · -- at most `MaxLen` bytes: reply, then close
    have hlen : (S.encOut v).length ≤ maxLen := by
      have key : ∀ (n : w64) (L : Nat), L = sint.nat n → 0 ≤ sint.Z n →
          uint.Z n ≤ uint.Z (W64 1048576) → L ≤ 2 ^ 20 := by
        intro n L h1 h2 h3; word
      exact key rep.len _ Hlen.1 Hlen.2 Hif
    wp_apply wp_deadline as %tm' -
    wp_apply wp_SetDeadline t cn true a la ra tm' (fun _ => iprop(True)) as %err' -
    · iframe Hca
      imod deadline_au cn true _ _ $$ Hci with ⟨%st, Hst, Hk⟩
      imodintro
      iexists st
      iframe Hst
      iintro %res %st' %Hdo Hst'
      imod Hk $$ %res %st' %Hdo Hst' with -
      imodintro
      itrivial
    wp_apply wp_writeFrame _ cn true a (repP S) [] rep (S.encOut v) (DFrac.own 1) ed hlen
      $$ [Hrepb Hsend] as %okw -
    · iframe Hc Hed Hrepb Hsend Hrep
    wp_apply wp_Close t cn true a la ra (fun _ => iprop(True)) as %err'' -
    · iframe Hca
      imod close_au cn true $$ Hci with ⟨%st, %dd, Hst, Hd, Hk⟩
      imodintro
      iexists st, dd
      iframe Hst Hd
      iintro %res %st' %d' %Hco Hst' Hd'
      imod Hk $$ %res %st' %d' %Hco Hst' Hd' with -
      imodintro
      itrivial
    iapply HΦ
    iexact Htok
  · -- too long: close
    wp_apply wp_Close t cn true a la ra (fun _ => iprop(True)) as %err' -
    · iframe Hca
      imod close_au cn true $$ Hci with ⟨%st, %dd, Hst, Hd, Hk⟩
      imodintro
      iexists st, dd
      iframe Hst Hd
      iintro %res %st' %d' %Hco Hst' Hd'
      imod Hk $$ %res %st' %d' %Hco Hst' Hd' with -
      imodintro
      itrivial
    iapply HΦ
    iexact Htok

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
