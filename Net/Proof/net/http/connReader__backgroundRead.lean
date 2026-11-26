/-
The proof of `connReader.backgroundRead` (`Net/Spec/net/http/connReader__backgroundRead.lean`): the
`Read` of one byte by `Conn.Read.spec` with the library's `read_au` (the reader's token past `hs` by
what it read: nothing, or a byte with the dialer's protocol fact, which `headLaw` turns into `Z cn`);
then under the mutex the phase is the background one with `inRead` set (the background reader's
token is ours), and the fields, the token and the reader's resources go back.
-/
module

public import Net.Spec.net.http.connReader__backgroundRead
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.OpError__Timeout
public import Net.Proof.net.http.ConnReaderLemmas
public import GooseLang.Ext.Net.Proto

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS] [net.Assumptions]

/-- A one-element slice of an array's place is the array. -/
theorem slice1_array (l : Loc) (xs : List w8) :
    (slice.mk l (W64 1) (W64 1) ↦* xs : IProp GF) ⊢
      ∃ arr : GoArray w8 1, typedPointsto l arr (DFrac.own 1) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (⟨%h, -⟩ | ⟨H, -⟩)
  · simp [slice.nil] at h
  · have h1 : sint.Z (W64 1) = 1 := by decide
    rw [h1]
    iexists (array.mk 1 xs)
    iexact H

/-- What the dialer wrote past its head gives `Z cn` (`headLaw`). -/
theorem law_Z (P : Proto GF) (hs : List w8) (Z : Nat → IProp GF) (cn : Nat) (R : List w8)
    (hR : ¬ R <+: hs) :
    headLaw P hs Z ∗ protoPrefix P cn R ⊢ Z cn := by
  unfold headLaw protoPrefix
  iintro ⟨#Hlaw, (%h | ⟨%ext, %hext, #HP⟩)⟩
  · subst h; exact absurd List.nil_prefix hR
  · icases Hlaw $$ %cn %ext HP with (%h | HZ)
    · exact absurd (hext.trans h) hR
    · iexact HZ

theorem errorString_not_netError :
    go.typeSetContains (go.GoType.PointerType errors.errorString.ty) net.Error.ty = false := by
  go_type_set

theorem opError_netError :
    go.typeSetContains (go.GoType.PointerType net.OpError.ty) net.Error.ty = true := by
  go_type_set

theorem connReader.backgroundRead.wp_proof (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Timeout : net.OpError.Timeout.spec (GF := GF) (hG := hG)) :
    connReader.backgroundRead.spec (GF := GF) (hG := hG) := by
  intro cr γ t cn a la ra P hs Z arr
  wp_start as ⟨#Hcr, #Hlaw, #Henv, #Hrwc, #Hca, Htok, Hbuf, Hrecv⟩
  iunfold readEnv at Henv
  icases Henv with ⟨#HEOF, ⟨%ed, #Hed⟩, -⟩
  unfold errors.newVar
  icases HEOF with ⟨%xe, #Hxe, -⟩
  obtain ⟨xs⟩ := arr
  ihave %Hn := array_len _ _ _ _ $$ Hbuf
  ihave Hs := slice_array (V := w8) _ 1 (array.mk 1 xs) (by simp; omega) $$ Hbuf
  wp_auto
  have h0 : sint.Z (W64 0) = 0 := by decide
  have h10 : (W64 1 - W64 0 : w64) = W64 1 := by decide
  rw [h0, go.arrayIndexRef_0, h10]
  ihave HrL := recvTok_L (Gg := hG.goose_globalGS) cn true _ _ $$ Hrecv
  wp_apply +noauto wp_Read t cn true a la ra _ _ (interface.mkOk errors.errorString.ty.PointerType #xe)
      ed (fun res => iprop(recvTokL (Gg := hG.goose_globalGS) cn true P (hs ++ res.got) ∗
        ⌜∃ st d d', ReadOutcome st d 1 res d'⌝))
      $$ [Hs HrL]
    as %k %err ⟨%res, %bs', ⟨HrL, %Hro⟩, Hs, %Hout, HE⟩
  · ihave #Hio' := net.connAt_io _ _ _ _ _ _ $$ Hca
    ihave #Hpoll := net.connAt_poll _ _ _ _ _ _ $$ Hca
    (try iframe Hio'); (try iframe Hpoll); iframe Hca Hs Hxe Hed
    imod read_au (Gg := hG.goose_globalGS) cn true _ _ 1 $$ HrL
      with ⟨%st, %d, HE, HD, Hcl⟩
    imodintro
    iexists st, d
    iframe HE HD
    iintro %r' %d' %Hrd HE HD
    iapply Hcl $$ %r' %d' %Hrd HE HD
  wp_auto
  wp_apply wp_cr_lock cr γ cn P hs Z $$ [$Hcr] as ⟨Hown, ⟨%cv, #Hcond⟩, Hph⟩
  iunfold crPh at Hph
  icases Hph with ⟨%ph, Hphv, Hph⟩
  cases ph
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso
    iapply token_exclusive $$ Htok Hph
  simp only [↓reduceIte]
  iunfold crBg at Hph
  icases Hph with ⟨%c, %hb, %ir, %ab, Hc, Hhb, Hir, Hab, Hr, #Hcok, Hrest⟩
  cases ir
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hrest with ⟨Htok2, -⟩
    iexfalso
    iapply token_exclusive $$ Htok Htok2
  simp only [↓reduceIte]
  icases Hrest with %Hhb
  subst Hhb
  have Hgl := readOutcome_got_le (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec Hro)))
  rcases res with bs | _ | kerr
  · -- a byte
    have Hpos := readOutcome_bytes_pos (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec Hro))) (by omega)
    obtain ⟨b, rfl⟩ : ∃ b, bs = [b] := by
      simp only [ReadRes.got] at Hgl
      match bs, Hpos, Hgl with
      | [b], _, _ => exact ⟨b, rfl⟩
    simp only [net.ReadOut] at Hout
    simp only [net.ReadErr]
    icases HE with %HE
    subst HE
    have hk : k = W64 1 := by
      have h1 := Hout.1
      simp only [List.length_singleton] at h1
      word
    subst hk
    simp only [decide_true]
    wp_auto
    icases recvTokL_proto (Gg := hG.goose_globalGS) cn true _ _ $$ HrL with ⟨HrL, #Hpp⟩
    ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn true _ _ $$ HrL
    icases slice1_array _ _ $$ Hs with ⟨%arr', Hs⟩
    wp_apply wp_cr_unlock cr γ cn P hs Z cv
      $$ [$Hcr $Hown $Hcond Hphv Hc Hhb Hir Hab Hr Htok Hs HrT]
    · iunfold crPh
      iexists true
      iframe Hphv
      simp only [↓reduceIte]
      iunfold crBg
      iexists c, true, false, false
      iframe Hc Hhb Hir Hab Hr Hcok
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Htok
      iunfold crRead
      isplitl [Hs]
      · iexists arr'; iexact Hs
      iexists (hs ++ [b])
      simp only [ReadRes.got]
      iframe HrT
      iright
      iapply law_Z P hs Z cn (hs ++ [b]) (fun h => by
        have := h.length_le; simp at this; omega) $$ [$Hlaw $Hpp]
    iunfold crCond at Hcond
    icases Hcond with ⟨-, #Hcf, #Hcv⟩
    wp_auto
    wp_apply sync.Cond.wp_Broadcast $$ [$Hcv]
    iapply HΦ; itrivial

  · -- EOF
    simp only [net.ReadOut] at Hout
    obtain ⟨rfl, rfl⟩ := Hout
    simp only [net.ReadErr]
    icases HE with %HE
    subst HE
    wp_auto
    simp only [errorString_not_netError, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply wp_handleReadErrorLocked cr c _ $$ [$Hc $Hcok] as Hc
    ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn true _ _ $$ HrL
    icases slice1_array _ _ $$ Hs with ⟨%arr', Hs⟩
    wp_apply wp_cr_unlock cr γ cn P hs Z cv
      $$ [$Hcr $Hown $Hcond Hphv Hc Hhb Hir Hab Hr Htok Hs HrT]
    · iunfold crPh
      iexists true
      iframe Hphv
      simp only [↓reduceIte]
      iunfold crBg
      iexists c, false, false, false
      iframe Hc Hhb Hir Hab Hr Hcok
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Htok
      iunfold crRead
      isplitl [Hs]
      · iexists arr'; iexact Hs
      iexists hs
      simp only [ReadRes.got, List.append_nil]
      iframe HrT
      ileft; ipureintro; simp
    iunfold crCond at Hcond
    icases Hcond with ⟨-, #Hcf, #Hcv⟩
    wp_auto
    wp_apply sync.Cond.wp_Broadcast $$ [$Hcv]
    iapply HΦ; itrivial
  · -- a failure: an `*OpError`
    simp only [net.ReadOut] at Hout
    obtain ⟨rfl, rfl⟩ := Hout
    simp only [net.ReadErr, net.resErr]
    icases HE with ⟨%e, HE, #Hk, -, #Hsa, #Haa⟩
    unfold net.opErr
    icases HE with ⟨%pe, %nw, ⟨%HE, -⟩, #Hpe⟩
    subst HE
    ihave #HpollT := net.connAt_poll _ _ _ _ _ _ $$ Hca
    ihave %hed := net.edTyped_of_poll _ $$ [$HpollT $Hed]
    ihave #HownE := net.kindErr_netOwnErr _ _ _ e hed $$ Hk
    ihave #Hok : net.opErrOk (GF := GF) (net.OpError.mk go!"read" nw la ra e) $$ []
    · unfold net.opErrOk; iframe HownE Hsa Haa
    wp_auto
    simp only [opError_netError, ↓reduceIte]
    wp_auto
    cases ab
    · wp_auto
      wp_apply wp_handleReadErrorLocked cr c _ $$ [$Hc $Hcok] as Hc
      ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn true _ _ $$ HrL
      icases slice1_array _ _ $$ Hs with ⟨%arr', Hs⟩
      wp_apply wp_cr_unlock cr γ cn P hs Z cv
        $$ [$Hcr $Hown $Hcond Hphv Hc Hhb Hir Hab Hr Htok Hs HrT]
      · iunfold crPh
        iexists true
        iframe Hphv
        simp only [↓reduceIte]
        iunfold crBg
        iexists c, false, false, false
        iframe Hc Hhb Hir Hab Hr Hcok
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe Htok
        iunfold crRead
        isplitl [Hs]
        · iexists arr'; iexact Hs
        iexists hs
        simp only [ReadRes.got, List.append_nil]
        iframe HrT
        ileft; ipureintro; simp
      iunfold crCond at Hcond
      icases Hcond with ⟨-, #Hcf, #Hcv⟩
      wp_auto
      wp_apply sync.Cond.wp_Broadcast $$ [$Hcv]
      iapply HΦ; itrivial
    · wp_auto
      wp_apply wp_Timeout $$ [$Hpe $Hok] as %b -
      cases b
      · wp_auto
        wp_apply wp_handleReadErrorLocked cr c _ $$ [$Hc $Hcok] as Hc
        ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn true _ _ $$ HrL
        icases slice1_array _ _ $$ Hs with ⟨%arr', Hs⟩
        wp_apply wp_cr_unlock cr γ cn P hs Z cv
          $$ [$Hcr $Hown $Hcond Hphv Hc Hhb Hir Hab Hr Htok Hs HrT]
        · iunfold crPh
          iexists true
          iframe Hphv
          simp only [↓reduceIte]
          iunfold crBg
          iexists c, false, false, false
          iframe Hc Hhb Hir Hab Hr Hcok
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe Htok
          iunfold crRead
          isplitl [Hs]
          · iexists arr'; iexact Hs
          iexists hs
          simp only [ReadRes.got, List.append_nil]
          iframe HrT
          ileft; ipureintro; simp
        iunfold crCond at Hcond
        icases Hcond with ⟨-, #Hcf, #Hcv⟩
        wp_auto
        wp_apply sync.Cond.wp_Broadcast $$ [$Hcv]
        iapply HΦ; itrivial
      · wp_auto
        ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn true _ _ $$ HrL
        icases slice1_array _ _ $$ Hs with ⟨%arr', Hs⟩
        wp_apply wp_cr_unlock cr γ cn P hs Z cv
          $$ [$Hcr $Hown $Hcond Hphv Hc Hhb Hir Hab Hr Htok Hs HrT]
        · iunfold crPh
          iexists true
          iframe Hphv
          simp only [↓reduceIte]
          iunfold crBg
          iexists c, false, false, false
          iframe Hc Hhb Hir Hab Hr Hcok
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe Htok
          iunfold crRead
          isplitl [Hs]
          · iexists arr'; iexact Hs
          iexists hs
          simp only [ReadRes.got, List.append_nil]
          iframe HrT
          ileft; ipureintro; simp
        iunfold crCond at Hcond
        icases Hcond with ⟨-, #Hcf, #Hcv⟩
        wp_auto
        wp_apply sync.Cond.wp_Broadcast $$ [$Hcv]
        iapply HΦ; itrivial


end proof

end net.http
end Perennial
