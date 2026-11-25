/- Lean-first (no Rocq counterpart).

# `(*server).Bidi`'s proof

The loop keeps the two tokens at one list `R` (what was received was sent back). A request `m`
received at position `R.length` is `upAt γ R.length m`, which is `biDn`'s response at that position:
sent back. `io.EOF` ends the loop with `nil`; another error is returned. The comparison
`err == io.EOF` is defined: `io.EOF` is a `*errorString` (`io.eof_of_init`), and an error of the
stream of that type is a pointer (`streamErr`'s tree, `TreeTyped`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__Bidi
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

theorem server.Bidi.wp_proof : server.Bidi.spec (GF := GF) (hG := hG) := by
  intro s st γ Dn ci cd md
  wp_start as ⟨#Hst, #Hdn, HRt, HSt⟩
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hv := _root_.Perennial.io.eof_of_init $$ Hio
  iunfold _root_.Perennial.errors.newVar at Hv
  icases Hv with ⟨%x, #Heofp, #-, #-⟩
  iunfold srvStreamIs at Hst
  icases Hst with ⟨%si, %Hsi, #HRecv, #HSend, -⟩
  subst Hsi
  wp_auto
  ihave IH : iprop(∃ R : List GoString, "HRt" ∷ srvRecvTok (Req := strmMsg (GF := GF)) γ R ∗
      "HSt" ∷ srvSendTok (Rep := strmMsg (GF := GF)) γ R) $$ [HRt HSt]
  · iexists []
    iframe
  wp_for IH
  try wp_auto
  wp_bind (App (Val #(methods si.ty go!"Recv" si.v)) _)
  iapply HRecv $$ %R [HRt]
  · iexact HRt
  iintro !> %req %err Hres
  icases Hres with (⟨%Herr, %m, Hm, -, HRt⟩ | ⟨#Heof, %Hne, HRt, #Hcl⟩ |
    ⟨%Hne, #Hse, #Hso, HRt, -⟩)
  · -- a request: sent back
    subst Herr
    wp_auto
    iunfold srvRecvTok at HRt
    icases HRt with ⟨HRt, #Hlb⟩
    ihave #Hat : iprop(upAt (Req := strmMsg (GF := GF)) γ R.length m) $$ []
    · iapply (upLb_at (Req := strmMsg (GF := GF)) γ (R ++ [m]) R.length m (by simp))
      unfold upLb
      iexact Hlb
    wp_bind (App (Val #(methods si.ty go!"Send" si.v)) _)
    iapply HSend $$ %R %req %m [HSt Hm]
    · iframe
      iapply Hdn
      iexact Hat
    iintro !> %err2 Hres2
    icases Hres2 with (⟨%He2, HSt⟩ | ⟨%Hne2, #Hse2, #Hso2, %L', -, -⟩)
    · subst He2
      wp_auto
      wp_for_post
      iexists (R ++ [m])
      iframe
      iunfold srvRecvTok
      iframe
      iframe #
    · cases err2 with
      | nil => exact absurd rfl Hne2
      | ok e2 =>
        wp_auto
        iapply HΦ
        iapply go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk $$ Hso2
  · -- `io.EOF`: the end
    iunfold eofIs at Heof
    icombine Heof Heofp gives %Heq
    subst Heq
    wp_auto
    iapply HΦ
    iapply go_etcd_io.etcd.cache.v3.srvErrOk_nil
  · -- another error: returned (or, if it is `io.EOF`'s value, `nil`)
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
        wp_auto
        by_cases hlx : l = x
        · subst hlx
          wp_auto
          iapply HΦ
          iapply go_etcd_io.etcd.cache.v3.srvErrOk_nil
        · wp_auto
          iapply HΦ
          iapply go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk $$ Hso
      · wp_auto
        iapply HΦ
        iapply go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk $$ Hso

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
