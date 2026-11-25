/- Lean-first (no Rocq counterpart).

# `(*server).ServerStream`'s proof

The receiver's token at `[v]` says the first request is `v` (`upAt γ 0 v`). The loop sends, at
position `i`, `v[i:i+1]` (Go's string slice: `(v.drop i).take 1`), `ssDn`'s response there; the
sender's token is at a list of length `i`. A failed send's error is returned.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__ServerStream
public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

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

theorem server.ServerStream.wp_proof
    (wp_String : google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG)) :
    server.ServerStream.spec (GF := GF) (hG := hG) := by
  intro s r v st γ Dn ci cd md
  wp_start as ⟨Hr, Hst, #Hdn, HRt, HSt⟩
  iunfold srvStreamIs at Hst
  icases Hst with ⟨%si, %Hsi, -, #HSend, -⟩
  subst Hsi
  iunfold srvRecvTok at HRt
  icases HRt with ⟨-, #Hlb⟩
  iunfold stringValueSend at Hr
  iunfold stringValueSendB at Hr
  icases Hr with ⟨%sv, Hsv, %Hsvp⟩
  obtain ⟨hval, -, hlen⟩ := Hsvp
  subst hval
  icases typedPointsto_split _ _ _ $$ Hsv with Hsv
  simp only [TypedPointsto.typedPointstoDef]
  icases Hsv with ⟨-, HV, -, -, -⟩
  wp_auto
  ihave IH : iprop(∃ (k : w64) (L : List GoString), "i" ∷ i_ptr ↦ k ∗
      "HSt" ∷ srvSendTok (Rep := strmMsg (GF := GF)) γ L ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ sv.Value'.length ∧ L.length = sint.nat k⌝) $$ [i HSt]
  · iexists W64 0, []
    iframe
    ipureintro
    refine ⟨by word, by simp, by first | rfl | decide | simp⟩
  wp_for IH
  have hlen' : sv.Value'.length < 2 ^ 30 := hlen
  try wp_auto
  wp_apply (_root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len
    sv.Value') as %Hslen
  wp_if_destruct
  · have hc : sint.Z k < sint.Z (W64 (sv.Value'.length : Int)) :=
      of_decide_eq_true (go.intoVal_inj Hif)
    split
    · rename_i hb
      have h1 : sint.nat (k + W64 1) - sint.nat k = 1 := by word
      rw [h1]
      try wp_auto
      wp_apply wp_String stringValueMax ((sv.Value'.drop (sint.nat k)).take 1)
        (Nat.lt_of_le_of_lt (List.length_take_le _ _) (by decide)) as %l Hl
      try wp_auto
      wp_bind (App (Val #(methods si.ty go!"Send" si.v)) _)
      iapply HSend $$ %L %l %((sv.Value'.drop (sint.nat k)).take 1) [HSt Hl]
      · isplitl [HSt]
        · iexact HSt
        isplitl [Hl]
        · iexact Hl
        iapply Hdn
        unfold ssDn
        iexists sv.Value'
        isplitr
        · iapply (upLb_at (Req := strmMsg (GF := GF)) γ [sv.Value'] 0 sv.Value' rfl)
          unfold upLb
          iexact Hlb
        ipureintro
        rw [Hk.2.2]
        exact ⟨by word, rfl⟩
      iintro !> %err Hres
      icases Hres with (⟨%He, HSt⟩ | ⟨%Hne, #Hse, #Hso, %L', -, -⟩)
      · subst He
        wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, L ++ [(sv.Value'.drop (sint.nat k)).take 1]
        iframe
        ipureintro
        refine ⟨by word, by word, by simp [Hk.2.2]; word⟩
      · cases err with
        | nil => exact absurd rfl Hne
        | ok e =>
          wp_auto
          wp_for_post
          iapply HΦ
          iapply go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk $$ Hso
    · rename_i hb
      exfalso
      apply hb
      refine ⟨by word, by word, by word⟩
  · have hc : decide (sint.Z k < sint.Z (W64 (sv.Value'.length : Int))) = false :=
      go.intoVal_inj Hif
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    iapply HΦ
    iapply go_etcd_io.etcd.cache.v3.srvErrOk_nil

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
