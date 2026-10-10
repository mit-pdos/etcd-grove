/-
`status.FromError(err)` (grpc, not translated: names only), and the `Code()` of its result. The
trust boundary (an axiom, `Proof/google_golang_org/grpc/status/FromError.lean`), for
`client/v3/leasing`'s `acquire`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `status.FromError(err)`: some `*Status` `s` and a boolean, and `s.Code()` returns (some code). -/
abbrev status.FromError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status }}
    (App (Val (@! google_golang_org.grpc.status.FromError)) (Val #err))
  {{ (s : Loc) (ok : Bool), RET (PairV #s #ok);
      □ (∀ Φ : val → IProp GF, ▷ (∀ c : w32, Φ #c) -∗
        WP (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.status.Status.ty @!! go!"Code"))
          (Val #())) {{ Φ }}) }}

end spec

end EtcdGrove
end Perennial
