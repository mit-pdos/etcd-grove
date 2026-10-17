/-
`jwt.Parse` (`github.com/golang-jwt/jwt/v5`, names only): the trust boundary of the JWT token
provider's `info` (PR etcd#21909). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.golang_jwt.jwt.v5.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI jwt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `jwt.Parse(s, keyFunc, opts...)`, with a key function whose calls (on a `*jwt.Token`
`Parse` owns) return a key and an error, returns an error, or a parsed token (`jwtTokenRO`: its
`Claims` and `Valid` read-only, map claims of JSON values). Nothing about the signature or the
claims' values: the callers' proofs do not need it. -/
abbrev jwt.Parse.spec : Prop :=
  ∀ (s : GoString) (kf : val) (opts : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.golang_jwt.jwt.v5 ∗
      □ (∀ tok : Loc, {{ True }} (App (Val kf) (Val #tok))
          {{ (k e : GoInterface), RET (PairV #k #e); True }}) }}
    (App (App (App (Val (@! github_com.golang_jwt.jwt.v5.Parse)) (Val #s)) (Val kf)) (Val #opts))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ jwtTokenRO p) }}

end spec

end EtcdGrove
end Perennial
