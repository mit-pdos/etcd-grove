/- Lean-first (no Rocq counterpart).

# `(*server).ClientStream`'s proof

The loop keeps `got` the concatenation of the requests `R` received (each at most one byte, at most
16 of them: `csUp`). At `io.EOF` the client closed after `R` (`upClosed γ R`): `got` is `csDn`'s
response, sent with `SendAndClose`. Another error is returned; it is not `io.EOF`'s value
(`srvNotEof`), so the comparison `err == io.EOF` is `false` (and defined: an error of the stream of
`io.EOF`'s type is a pointer, `streamErr`'s tree).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__ClientStream
public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem server.ClientStream.wp_proof
    (wp_String : google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG)) :
    server.ClientStream.spec (GF := GF) (hG := hG) := by
  intro s st γ Dn ci cd md
  wp_start as ⟨#Hst, #Hsac, #Hdn, HRt, HSt⟩
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hv := _root_.Perennial.io.eof_of_init $$ Hio
  iunfold _root_.Perennial.errors.newVar at Hv
  icases Hv with ⟨%x, #Heofp, #-, #-⟩
  iunfold srvStreamIs at Hst
  icases Hst with ⟨%si, %Hsi, #HRecv, -, -⟩
  subst Hsi
  iunfold svc.sacOk at Hsac
  icases Hsac with ⟨%si', %Hsi', #HSac⟩
  have hsi : si = si' := by injection Hsi'
  subst hsi
  wp_auto
  ihave IH : iprop(∃ (R : List (strmMsg (GF := GF)).M) (g : GoString), "got" ∷ got_ptr ↦ g ∗
      "HRt" ∷ srvRecvTok (Req := strmMsg (GF := GF)) γ R ∗
      "%Hg" ∷ ⌜g = List.flatten R ∧ g.length ≤ R.length ∧ R.length ≤ 16⌝) $$ [got HRt]
  · iexists [], go!""
    iframe
    ipureintro
    exact ⟨rfl, by simp, by simp⟩
  wp_for IH
  try wp_auto
  wp_bind (App (Val #(methods si.ty go!"Recv" si.v)) _)
  iapply HRecv $$ %R [HRt]
  · iexact HRt
  iintro !> %req %err Hres
  icases Hres with (⟨%Herr, %m, Hm, HUp, HRt⟩ | ⟨#Heof, %Hne, HRt, Hcl⟩ |
    ⟨%Hne, #Hse, #Hso, HRt, #Hnot⟩)
  · -- a request: appended
    subst Herr
    iunfold csUp at HUp
    icases HUp with %HUp
    isimp only [strmMsg, pbStringValueST, pbStringValueS, stringValueSend, stringValueSendB] at Hm
    icases Hm with ⟨%sv, Hsv, %Hsvp⟩
    obtain ⟨hval, -, -⟩ := Hsvp
    subst hval
    iStructNamed Hsv
    wp_auto
    wp_for_post
    iframe
    iexists R ++ [sv.Value'], g ++ sv.Value'
    iframe
    ipureintro
    refine ⟨by simp [Hg.1], by simp; omega, by simp; omega⟩
  · -- `io.EOF`: the client closed after `R`
    iunfold eofIs at Heof
    icombine Heof Heofp gives %Heq
    subst Heq
    wp_auto
    wp_apply wp_String stringValueMax g (by unfold stringValueMax; omega) as %l Hl
    try wp_auto
    wp_bind (App (Val #(methods si.ty go!"SendAndClose" si.v)) _)
    iapply HSac $$ %([] : List (strmMsg (GF := GF)).M) %l %g [HSt Hl Hcl]
    · isplitl [HSt]
      · iexact HSt
      isplitl [Hl]
      · iexact Hl
      iapply Hdn
      unfold csDn
      isplitr
      · ipureintro; rfl
      iexists R
      iframe Hcl
      ipureintro; exact Hg.1
    iintro !> %err2 Hres2
    icases Hres2 with (⟨%He2, -⟩ | ⟨%Hne2, #Hse2, #Hso2, -⟩)
    · subst He2
      wp_auto
      wp_for_post
      iapply HΦ
      iapply go_etcd_io.etcd.cache.v3.srvErrOk_nil
    · wp_auto
      wp_for_post
      iapply HΦ
      iapply go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk $$ Hso2
  · -- another error: not `io.EOF`'s value; returned
    ihave #Heo : iprop(eofIs (interface.mkOk (go.GoType.PointerType
        _root_.Perennial.errors.errorString.ty) #x)) $$ []
    · iunfold eofIs
      iexact Heofp
    iunfold srvNotEof at Hnot
    ihave %Hnx := Hnot $$ %(interface.mkOk (go.GoType.PointerType
      _root_.Perennial.errors.errorString.ty) #x) Heo
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      iunfold streamErr at Hse
      icases Hse with ⟨-, #Htree⟩
      ihave ⟨%Sx, %Mx, -, %HS⟩ := Htree $$
        %(interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x)
      have htt := HS.2 (fun tii h => by cases h; exact ⟨_, x, rfl, rfl⟩)
      by_cases hty : ei.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty
      · obtain ⟨l, hl⟩ := htt ei ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
          HS.1 rfl hty
        obtain ⟨ety, ev⟩ := ei
        simp only at hty hl
        subst hty hl
        have hlx : l ≠ x := fun h => Hnx (by subst h; rfl)
        wp_auto
        try rw [if_pos rfl]
        try wp_auto
        wp_for_post
        iapply HΦ
        iapply go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk $$ Hso
      · wp_auto
        try rw [if_neg hty]
        try wp_auto
        wp_for_post
        iapply HΦ
        iapply go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk $$ Hso

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
