/-
`newTokenProviderNop()` (`server/auth/nop.go`): the no-op token provider's constructor, for
`NewTokenProvider`. Lean-first (no Rocq counterpart); the auth plan's E2g (2026-10-25).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `newTokenProviderNop()`: a fresh `*tokenNop`, and no error. -/
abbrev auth.newTokenProviderNop.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth }}
    (App (Val (@! go_etcd_io.etcd.server.v3.auth.newTokenProviderNop)) (Val #()))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err); ⌜err = GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
