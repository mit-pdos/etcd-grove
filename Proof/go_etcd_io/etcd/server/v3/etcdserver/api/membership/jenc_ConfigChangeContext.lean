/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/jenc_ConfigChangeContext.lean` (jsongen's generated
code, membership's `json_model_gen.go`), over `models.lab/jsoncodec`'s proved helpers.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.jenc_ConfigChangeContext
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.jenc_S_string
public import Net.Spec.models_lab.jsoncodec.AppendString
public import Net.Spec.models_lab.jsoncodec.AppendRaw
public import Net.Spec.models_lab.jsoncodec.AppendUint
public import Net.Spec.models_lab.jsoncodec.AppendBool

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

set_option goose.wp.extras true

open go_etcd_io.etcd.server.v3.etcdserver.api in
set_option maxHeartbeats 2000000 in
theorem membership.jenc_ConfigChangeContext.wp_proof
    (wp_S : membership.jenc_S_string.spec (GF := GF) (hG := hG))
    (wp_AppendString : models_lab.jsoncodec.AppendString.spec (GF := GF) (hG := hG))
    (wp_AppendRaw : models_lab.jsoncodec.AppendRaw.spec (GF := GF) (hG := hG))
    (wp_AppendUint : models_lab.jsoncodec.AppendUint.spec (GF := GF) (hG := hG))
    (wp_AppendBool : models_lab.jsoncodec.AppendBool.spec (GF := GF) (hG := hG)) :
    membership.jenc_ConfigChangeContext.spec (GF := GF) (hG := hG) := by
  intro b bs c dp dc ps cs d hd
  wp_start as ⟨Hb, Hcap, Hp, Hc⟩
  ihave %Hclen := ownSlice_len _ _ _ $$ Hc
  wp_auto
  wp_if_destruct
  · exfalso
    have : uint.Z (W64 10000) = 10000 := rfl
    omega
  have hd1 : uint.Z (d + W64 1) < 1000 := by word
  cases hlearn : c.Member'.RaftAttributes'.IsLearner'
  all_goals repeat' (first
    | wp_if_destruct
    | (rw [hlearn])
    | wp_auto
    | wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hnl
    | wp_apply wp_AppendRaw $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply wp_AppendUint $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply wp_AppendBool $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply wp_AppendString $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (wp_S _ _ _ _ _ _ hd1) $$ [$Hb $Hcap $Hp] as %b' ⟨Hb, Hcap, Hp⟩
    | wp_apply (wp_S _ _ _ _ _ _ hd1) $$ [$Hb $Hcap $Hc] as %b' ⟨Hb, Hcap, Hc⟩
    | (wp_apply wp_slice_literal (V := w8)
       isplitr
       · ipureintro; rfl
       iintro %lsl ⟨Hlsl, -⟩
       wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlsl] as %b' ⟨Hb, Hcap, -⟩))
  all_goals
    iapply HΦ
    iframe
    iapply (models_lab.jsoncodec.slice_pts_eq _ _ _ ?_) $$ Hb
    simp only [membership.strlen_w64_iff _ hnl, membership.slicelen_w64_iff _ _ Hclen] at *
    unfold membership.ccJson membership.memberFieldsJson
    simp_all

end proof

end EtcdGrove
end Perennial
