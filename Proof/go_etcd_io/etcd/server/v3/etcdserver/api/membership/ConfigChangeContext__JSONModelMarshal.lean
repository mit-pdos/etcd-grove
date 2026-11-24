/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/ConfigChangeContext__JSONModelMarshal.lean` (jsongen's generated
code, membership's `json_model_gen.go`), over `models.lab/jsoncodec`'s proved helpers.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext__JSONModelMarshal
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.jenc_ConfigChangeContext

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
theorem membership.ConfigChangeContext.JSONModelMarshal.wp_proof
    (wp_enc : membership.jenc_ConfigChangeContext.spec (GF := GF) (hG := hG)) :
    membership.ConfigChangeContext.JSONModelMarshal.spec (GF := GF) (hG := hG) := by
  intro jr c dp dc ps cs
  wp_start as ⟨Hp, Hc⟩
  wp_auto
  wp_apply wp_slice_make2 (V := w8) (W64 0) as %sl ⟨Hsl, Hcap⟩
  · ipureintro; word
  wp_apply (wp_enc _ _ c dp dc ps cs (W64 0) (by word)) $$ [$Hsl $Hcap $Hp $Hc]
    as %b' ⟨Hb, Hcap, Hp, Hc⟩
  try wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
