/-
`types.ID.String` (`id.go`: `strconv.FormatUint(uint64(i), 16)`), verified: translated with its
body (`Code/go_etcd_io/etcd/client/pkg/v3/types.toml`), over `strconv.FormatUint`'s spec. Its result
is `types.idStr id`, which is `fmtUint id 16` (`types.idStr_fmtUint`, `IDStr.lean`). Until
2026-11-18 a trust-boundary axiom (`client/pkg/v3/types` was names-only).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.strconv.FormatUint

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

theorem types.ID.String.wp_proof (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    types.ID.String.spec (GF := GF) (hG := hG) := by
  intro id
  wp_start
  wp_auto
  wp_apply wp_FormatUint as %str %Hstr
  · ipureintro; decide
  iapply HΦ
  ipureintro
  rw [Hstr, types.idStr_fmtUint]

end proof

end EtcdGrove
end Perennial
