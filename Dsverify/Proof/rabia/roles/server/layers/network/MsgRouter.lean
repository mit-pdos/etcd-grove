/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/network/MsgRouter.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/roles/server/layers/network.(*Network).MsgRouter`.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.network.Basics
public import Dsverify.Proof.rabia.internal.message.Marshal

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.network

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia rabia.internal.tcp

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.layers.network.Assumptions]

set_option goose.wp.extras true

set_option maxHeartbeats 4000000 in
theorem Network.MsgRouter.wp_of (hM : Msg.Marshal.spec (GF := GF)) :
    Network.MsgRouter.spec (GF := GF) := fun γ cf k γl ch n => by
  wp_start as ⟨#Hconf, #Hsh, #Hcfg, Hres⟩
  ihave %hnS := cfgIs_n_le γ cf $$ Hcfg
  unfold networkRouterRes
  icases Hres with ⟨%nv, %γr, %γts, %γsl, %γs, %Hf, #Hn, #Hch, #Hrecv, #Hsend, #Hts, Hloop⟩
  wp_apply wp_with_defer as %defer Hdefer
  iStructNamed Hn
  wp_auto
  obtain ⟨hk, hDone, hP, hH, hE, hNH, hNE⟩ := Hf
  unfold srvChans
  icases Hch with ⟨#Hdone, -, #Hp2n, -, #Hh2n, #Hie2n, #Hin2h, #Hn2e⟩
  unfold netTcpRecv
  icases Hrecv with ⟨%rc, #Hrc, #Hrco⟩
  unfold netTcpSend
  icases Hsend with ⟨%ssl, %chs, #Hssl, #Hchs, %Hlens, #Hchans⟩
  wp_for_core
  wp_auto
  cleanup_bool_decide
  wp_auto_lc 4
  rw [hDone, hP, hH, hE]
  wp_apply_core chan.wp_select_blocking
  unfold routerLoop
  icases Hloop with ⟨%P, %E, %T, %H, %bl, %hl, Hcons, %HPl, #Hpush, He2n, Hts', Hsa, %Hbl, Hn2h,
    Hha, %Hhl, Hprods⟩
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `Done`: nothing is sent on it
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch.done, γl.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hdone
    iapply bag_recv_au _ _ _ _ $$ [$Hlc1 $Hlc2] Hdone
    inext
    iintro %v Hv
    unfold doneP
    iexfalso; iexact Hv
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `ProxyIn`: a client request, forwarded to the serializer
    simp only [chan.blockingClausePre]
    iexists Msg, inferInstance, inferInstance, inferInstance, inferInstance, ch.p2n, γl.p2n
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hp2n
    iapply bag_recv_au _ _ _ _ $$ [$Hlc1 $Hlc2] Hp2n
    inext
    iintro %v Hv
    unfold p2nP
    icases Hv with ⟨%m, %o, %Hmo, #Hrep, Hok, Htok⟩
    imod serAuth_snoc ⊤ γsl bl false $$ Hsa with ⟨Hsa, #Hlb⟩
    wp_auto
    wp_apply wp_spsc_send γts nv.ToSerializer' (toSerP γ cf k γl γsl) (fun _ => iprop(False)) T v $$
      [$Hts $Hts' Htok Hok] as Hts'
    · unfold toSerP
      iexists m, bl ++ [false]
      have h1 : (bl ++ [false])[((T.length : Int)).toNat]? = some false := by simp [Hbl.1]
      simp only [h1, Option.some.injEq, Bool.false_eq_true, ↓reduceIte]
      iframe Hrep Hok Hlb
      isplitr
      · ipureintro; simp [Hbl.1]
      iexists o
      iframe Htok
      ipureintro; exact Hmo
    wp_for_post
    iframe
    iexists P, E, T ++ [v], H, bl ++ [false], hl
    iframe
    isplitr
    · ipureintro; exact HPl
    isplitr
    · iexact Hpush
    isplitr
    · ipureintro; simp [Hbl]
    ipureintro; exact Hhl
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `MsgHandlerIn`: a `ProposalReply`, encoded and sent to its server `Phase` (producer 1)
    simp only [chan.blockingClausePre]
    iexists Msg, inferInstance, inferInstance, inferInstance, inferInstance, ch.h2n, γl.h2n
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hh2n
    iapply bag_recv_au _ _ _ _ $$ [$Hlc1 $Hlc2] Hh2n
    inext
    iintro %v Hv
    unfold h2nP
    icases Hv with ⟨%m, %j, %hj, #Hrep, Hok⟩
    icases replyOk_encBound γ cf j m $$ Hok with ⟨Hok, %Hbnd⟩
    wp_auto
    wp_apply hM msg_ptr v m (DFrac.own 1) $$ [$msg $Hrep] as %dsl ⟨msg, Hd⟩
    · ipureintro; exact Hbnd
    ihave %Hf := msgRep_fields v m $$ Hrep
    ihave %Hchslen := ownSlice_len _ _ _ $$ Hchs
    icases replyOk_phase γ cf j m $$ Hok with ⟨Hok, %Hph⟩
    have hjZ : sint.Z (W64 (uint.Z v.Phase')) = (j : Int) := by
      rw [Hf.2.1, ← Hph]; have : j < 5 := by unfold maxS at hnS; omega
      word
    have Hid : 0 ≤ sint.Z (W64 (uint.Z v.Phase')) ∧ sint.Z (W64 (uint.Z v.Phase')) < sint.Z ssl.len := by
      have hlen : sint.Z ssl.len = (cf.n : Int) := by
        have h1 := Hchslen.1; rw [Hlens.1] at h1; have h2 := Hchslen.2
        unfold maxS at hnS; word
      rw [hjZ, hlen]; omega
    simp only [Hid, _root_.and_self, ↓reduceIte]
    obtain ⟨cj, Hcj⟩ : ∃ cj, chs[j]? = some cj := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨γo, Hγo⟩ : ∃ γo, γs[j]? = some γo := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_slice_index ssl (sint.Z (W64 (uint.Z v.Phase'))) chs _ cj Hid.1 $$ [$Hchs] as -
    · ipureintro; rw [hjZ]; simpa using Hcj
    ihave #Hcho := BigSepL.bigSepL_lookup Hcj $$ Hchans
    icases Hcho with ⟨%γo', %Hγo', #Hcho⟩
    rw [Hγo] at Hγo'; cases Hγo'
    iapply fupd_wp
    imod (ownSlice_persist dsl _ _) $$ Hd with #Hd
    imodintro
    icases (BigSepL.bigSepL_lookup_acc Hγo).1 $$ Hprods with ⟨⟨%c, Hprod⟩, Hprods⟩
    wp_apply wp_ord_send γo cj 2 (sendP γ cf k j) 1 c dsl $$ [$Hcho $Hprod Hok] as Hprod
    · unfold sendP
      simp only [Nat.one_ne_zero, ↓reduceIte]
      iexists m
      iframe Hd Hok
    wp_for_post
    iframe
    iexists P, E, T, H, bl, hl
    iframe
    isplitr
    · ipureintro; exact HPl
    isplitr
    · iexact Hpush
    isplitr
    · ipureintro; exact Hbl
    isplitr
    · ipureintro; exact Hhl
    ihave Hprods := Hprods $$ %γo [Hprod]
    · iexists c + 1; iexact Hprod
    rw [list_set_lookup_self γs j γo Hγo]
    iexact Hprods
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `ConExecutorIn`: the executor's next message, forwarded to the serializer in order
    simp only [chan.blockingClausePre]
    iexists Msg, inferInstance, inferInstance, inferInstance, inferInstance, ch.e2n, γl.e2n.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isSpsc; icases Hie2n with ⟨$, -⟩
    iapply spsc_rcv_au γl.e2n ch.e2n (e2nP γ cf k γl) (fun _ => iprop(False)) E _ $$ Hie2n [$Hlc1 $Hlc2] He2n
    inext
    iintro %v %ok Hv
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨Hv, -⟩
      iexfalso; iexact Hv
    simp only [↓reduceIte]
    icases Hv with ⟨Hv, He2n⟩
    unfold e2nP
    icases Hv with ⟨%m, %l, #Hrep, Hok, #Hexl, %Hl⟩
    imod serAuth_snoc ⊤ γsl bl true $$ Hsa with ⟨Hsa, #Hlb⟩
    wp_auto
    wp_apply wp_spsc_send γts nv.ToSerializer' (toSerP γ cf k γl γsl) (fun _ => iprop(False)) T v $$
      [$Hts $Hts' Hok] as Hts'
    · unfold toSerP
      iexists m, bl ++ [true]
      have h1 : (bl ++ [true])[((T.length : Int)).toNat]? = some true := by simp [Hbl.1]
      simp only [h1, ↓reduceIte]
      iframe Hrep Hok Hlb
      isplitr
      · ipureintro; simp [Hbl.1]
      iexists l
      iframe Hexl
      ipureintro
      have h2 : List.take ((T.length : Int)).toNat (bl ++ [true]) = bl := by simp [← Hbl.1]
      rw [h2, Hbl.2]
      simpa using Hl
    wp_for_post
    iframe
    iexists P, E ++ [v], T ++ [v], H, bl ++ [true], hl
    iframe
    isplitr
    · ipureintro; exact HPl
    isplitr
    · iexact Hpush
    isplitr
    · ipureintro; simp [Hbl]
    ipureintro; exact Hhl
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `RecvChan`: a peer's message, to the executor (a reply) or to the handler (a broadcast)
    simp only [chan.blockingClausePre]
    iexists Msg, inferInstance, inferInstance, inferInstance, inferInstance, rc, γr.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isOrdChan; icases Hrco with ⟨$, -⟩
    iapply ord_rcv_au γr rc cf.n (recvP γ cf k γl) (P.map List.length) _ $$ Hrco [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok %Hok Hv
    icases Hv with ⟨%X, %hX, Hv, Hcons⟩
    obtain ⟨px, Hpx⟩ : ∃ px, P[X]? = some px := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hf : (P.map List.length).getD X 0 = px.length := by simp [Hpx]
    unfold recvP
    icases Hv with ⟨%m, %lp, #Hrep, #Hplb, %Hlp, #Hbcl, Hrest⟩
    rw [hf] at Hlp
    ihave #Hpxlb := Hpush $$ %X %px %Hpx
    unfold pushLb
    ihave %Hpre := mono_list_lb_valid _ _ _ $$ Hpxlb Hplb
    have hlp : lp = px ++ [m] := snoc_of_prefix px lp m Hpre Hlp.1 Hlp.2
    subst hlp
    have Hcnt := map_length_set P X px (px ++ [m]) Hpx (by simp)
    rw [← Hcnt]
    ihave %Hf := msgRep_fields v m $$ Hrep
    wp_auto
    wp_if_destruct
    · -- a reply: to the executor
      have hty : m.ty = tyProposalReply := by rw [← Hf.1]; assumption
      simp only [bcastPart_snoc_reply _ _ hty, hty, ↓reduceIte]
      rw [hNE]
      wp_apply wp_bag_send γl.n2e ch.n2e v (n2eP γ cf k) $$ [$Hn2e Hrest]
      · unfold n2eP; iexists m; iframe Hrep Hrest
      wp_for_post
      iframe
      iexists P.set X (px ++ [m]), E, T, H, bl, hl
      iframe
      isplitr
      · ipureintro; simpa using HPl
      isplitr
      · imodintro
        iintro %Y %py %hy
        rw [List.getElem?_set] at hy
        by_cases hYX : X = Y
        · subst hYX
          have hlt : X < P.length := (List.getElem?_eq_some_iff.1 Hpx).1
          simp only [hlt, ↓reduceIte, Option.some.injEq] at hy
          subst hy
          iexact Hplb
        · simp only [hYX, ↓reduceIte] at hy
          iapply Hpush $$ %Y %py %hy
      isplitr
      · ipureintro; exact Hbl
      ipureintro
      exact ⟨Hhl.1, hlInv_same P hl X px (px ++ [m]) Hpx (bcastPart_snoc_reply _ _ hty) Hhl.2⟩
    · -- a broadcast: to the handler, with its receipt, after the sender's earlier ones
      have hty : m.ty ≠ tyProposalReply := by rw [← Hf.1]; assumption
      simp only [bcastPart_snoc_bc _ _ hty, hty, ↓reduceIte]
      icases Hrest with ⟨Hok, Hrc⟩
      imod hAuth_snoc ⊤ γl hl (X, (bcastPart px).length) $$ Hha with ⟨Hha, #Hhlb⟩
      rw [hNH]
      wp_apply wp_spsc_send γl.n2h ch.n2h (n2hP γ cf γl) (fun _ => iprop(False)) H v $$
        [$Hin2h $Hn2h Hok Hrc] as Hn2h
      · unfold n2hP
        iexists m, X, (bcastPart px).length, bcastPart px ++ [m], hl ++ [(X, (bcastPart px).length)]
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
        iframe Hrep Hbcl Hok Hrc Hhlb
        ipureintro
        refine ⟨by omega, by simp, by simp [Hhl.1], ?_, ?_⟩
        · simp [← Hhl.1]
        · intro j' hj'
          have h2 : List.take ((H.length : Int)).toNat (hl ++ [(X, (bcastPart px).length)]) = hl := by
            simp [← Hhl.1]
          rw [h2]
          exact Hhl.2 X px Hpx j' hj'
      wp_for_post
      iframe
      iexists P.set X (px ++ [m]), E, T, H ++ [v], bl, hl ++ [(X, (bcastPart px).length)]
      iframe
      isplitr
      · ipureintro; simpa using HPl
      isplitr
      · imodintro
        iintro %Y %py %hy
        rw [List.getElem?_set] at hy
        by_cases hYX : X = Y
        · subst hYX
          have hlt : X < P.length := (List.getElem?_eq_some_iff.1 Hpx).1
          simp only [hlt, ↓reduceIte, Option.some.injEq] at hy
          subst hy
          iexact Hplb
        · simp only [hYX, ↓reduceIte] at hy
          iapply Hpush $$ %Y %py %hy
      isplitr
      · ipureintro; exact Hbl
      ipureintro
      exact ⟨by simp [Hhl.1], hlInv_snoc P hl X px m Hpx Hhl.2⟩
  iapply BigAndL.bigAndL_nil.2
  itrivial

/-- `Network.MsgRouter.spec` (with C1's `Msg.Marshal.wp_proof`). -/
theorem Network.MsgRouter.wp_proof : Network.MsgRouter.spec (GF := GF) :=
  Network.MsgRouter.wp_of rabia.internal.message.Msg.Marshal.wp_proof

end proof
end Perennial.rabia.roles.server.layers.network
