/-
`hraftnet.awaitConf`'s proof (vr's `wp_awaitConf`, `vsrnet/ConfDefs.lean`, on one byte): `listen`,
then forever `Accept`, `io.ReadFull` of one byte (a prefix of the drawn size's, `confProto`), the
first size fulfilling the future, an acknowledgment, `Close`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.awaitConf
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.listen

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

theorem awaitConf.wp_proof (wp_listen : listen.spec (GF := GF))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG)) :
    awaitConf.spec (GF := GF) := by
  intro γc γf ch addr
  wp_start as ⟨#Hpr, #Hfut, Hful⟩
  ihave ⟨%eof, %ueof, %ed, %Hev, #Heof, #Hue, #Hed⟩ := errs_init $$ Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave %Hok := addrTok_ok addr $$ [Hpr]
  · iapply addrProto_tok $$ Hpr
  wp_auto
  wp_apply (wp_listen addr) as %lv ⟨%l, #Hl, Hlis, #Hla⟩
  · isplitr; · ipureintro; exact Hok
    imodintro
    iapply listen_au $$ Hpr
  try wp_auto
  unfold net.isListener
  icases Hl with ⟨%t, %x, %Ht, #Hlt⟩
  subst Ht
  ihave HI : (∃ (fst : Bool), "first" ∷ first_ptr ↦ fst ∗
      "Hful" ∷ (if fst then Fulfill γf (confOk (G := hG.goose_globalGS) γc) else True) : IProp GF)
    $$ [first Hful]
  · iexists true; iframe first; simp only [↓reduceIte]; iexact Hful
  wp_for HI
  cleanup_bool_decide
  wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l x addr
      (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l addr true)
      (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l addr true ∗
        connEnd (Gg := hG.goose_globalGS) cn true ackProto (confProto γc) [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn true))
      $$ [Hlis]
    as %cv %err (⟨%Herr, %cn, #Hc, Hlis, Hend, -⟩ | ⟨%k, Hlis, #Herr⟩)
  · iframe Hlt Hla
    iapply accept_au addr (confProto γc) ackProto _ l true $$ Hpr Hlis
  rotate_left
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Herr'
    obtain ⟨pe, rfl⟩ := Herr'.2 (by simp)
    wp_auto
    wp_for_post
    iframe
    iexists fst; iframe
  subst Herr
  unfold net.isConn
  icases Hc with ⟨%tc, %la, %ra, %Hct, #Hca⟩
  subst Hct
  iunfold connEnd at Hend
  icases Hend with ⟨Hs, Hrv⟩
  ihave #Hconn := sendTok_connIs cn true _ _ $$ Hs
  wp_auto
  ihave #Hrd := net.conn_readerOk wp_Read tc cn true addr la ra eof ed (confProto γc) $$ [$Hio $Hca $Heof $Hed]
  iunfold net.connIface at Hrd
  ihave Hrv := recvTok_L $$ Hrv
  ihave Hb := slice_array b_ptr 1 _ (by decide) $$ b
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show (W64 1 - W64 0) = W64 1 from rfl,
    show (zero_val (GoArray w8 1)).arr = [W8 0] from rfl]
  wp_apply io.wp_ReadFull ⟨go.GoType.PointerType net.TCPConn.ty, #tc⟩ (fun _ m => 0 < m)
      (recvTokL (Gg := hG.goose_globalGS) cn true (confProto γc)) (net.connReadE eof la ra ed) []
      (slice.mk b_ptr (W64 1) (W64 1)) [W8 0] eof ueof
      $$ [Hrv Hb] as %n2 %err2 ⟨%ys, %Hys, Hb, Hrv, #Hres⟩
  · iframe Hrd Heof Hue Hrv Hb; ipureintro; intro _ hl; simp only [List.length_cons, List.length_nil] at hl ⊢; omega
  iunfold io.readFullRes at Hres
  icases Hres with (%Hl | ⟨%e, %He, -⟩)
  rotate_left
  · have herr : err2 ≠ GoInterface.nil := by
      obtain ⟨-, hne, h1, h2⟩ := He
      by_cases hc : e = eof ∧ ys ≠ []
      · rw [h1 hc]; exact Hev.2
      · rw [h2 hc]; exact hne
    cases err2 with
    | nil => exact absurd rfl herr
    | ok i =>
    wp_auto
    wp_apply wp_closeConn wp_Close tc cn true addr la ra $$ [] as %e2 -
    · iframe Hca Hconn
    wp_for_post
    iframe
    iexists fst; iframe
  obtain ⟨hl, rfl⟩ := Hl
  obtain ⟨x1, rfl⟩ : ∃ x, ys = [x] := by
    match ys, hl with
    | [x], _ => exact ⟨x, rfl⟩
  rw [show List.drop [x1].length [W8 0] = [] from rfl, List.append_nil]
  wp_auto_lc 1
  rw [show arrayIndexRef w8 (sint.Z (W64 0)) b_ptr =
    sliceIndexRef w8 (sint.Z (W64 0)) (slice.mk b_ptr (W64 1) (W64 1)) from rfl]
  wp_apply wp_load_slice_index _ _ [x1] _ x1 (by decide) $$ [$Hb] as Hb
  · ipureintro; rfl
  try wp_auto
  wp_if_destruct
  · rw [List.nil_append]
    ihave Hrv := recvTokL_later $$ Hrv
    iapply fupd_wp
    imod (lc_fupd_elim_later (GF := GF) (E := ⊤)) $$ Hlc1 Hrv with Hrv
    imodintro
    ihave ⟨-, Hpp⟩ := recvTok_proto $$ Hrv
    ihave #Hok := conf_learn γc cn x1 $$ Hpp
    wp_if_destruct
    · cases fst
      · wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := w8) (t := go.byte) [W8 107]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %sl1 ⟨Hsl1, -⟩
        wp_auto
        ihave #Hp0 : (□ ackProto (GF := GF) cn ([] ++ [W8 107])) $$ []
        · iintro !>; unfold ackProto; itrivial
        wp_apply wp_Write tc cn true addr la ra _ [W8 107] _ ed
            (writeP (Gg := hG.goose_globalGS) cn true ackProto []) $$ [Hs Hsl1]
          as %nw %werr ⟨%w, %res, Hs, Hsl1, -, -⟩
        · iframe Hca Hsl1 Hed
          isplitl [Hs]
          · iapply writeP_init $$ Hs
          · iapply write_acc cn true ackProto [] _ $$ Hp0
        wp_auto
        wp_apply wp_closeConn wp_Close tc cn true addr la ra $$ [] as %e2 -
        · iframe Hca Hconn
        wp_for_post
        iframe
        iexists false; iframe first; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      · simp only [↓reduceIte]
        wp_auto
        wp_apply wp_future_fulfill (t := go.uint64) γf ch (W64 (uint.Z x1)) $$ [$Hfut Hful]
        · unfold Fulfilled; iexists _; iframe; iexact Hok
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := w8) (t := go.byte) [W8 107]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %sl1 ⟨Hsl1, -⟩
        wp_auto
        ihave #Hp0 : (□ ackProto (GF := GF) cn ([] ++ [W8 107])) $$ []
        · iintro !>; unfold ackProto; itrivial
        wp_apply wp_Write tc cn true addr la ra _ [W8 107] _ ed
            (writeP (Gg := hG.goose_globalGS) cn true ackProto []) $$ [Hs Hsl1]
          as %nw %werr ⟨%w, %res, Hs, Hsl1, -, -⟩
        · iframe Hca Hsl1 Hed
          isplitl [Hs]
          · iapply writeP_init $$ Hs
          · iapply write_acc cn true ackProto [] _ $$ Hp0
        wp_auto
        wp_apply wp_closeConn wp_Close tc cn true addr la ra $$ [] as %e2 -
        · iframe Hca Hconn
        wp_for_post
        iframe
        iexists false; iframe first; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    · try wp_auto
      wp_apply wp_closeConn wp_Close tc cn true addr la ra $$ [] as %e2 -
      · iframe Hca Hconn
      wp_for_post
      iframe
      iexists fst; iframe
  all_goals
    try wp_auto
    wp_apply wp_closeConn wp_Close tc cn true addr la ra $$ [] as %e2 -
    · iframe Hca Hconn
    wp_for_post
    iframe
    iexists fst; iframe

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
