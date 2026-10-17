/-
`schema.NewAuthBackend(lg, be)` (`auth.go`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `NewAuthBackend(lg, be)` returns an `auth.AuthBackend`: a fresh `*authBackend` wrapping `be`
(its fields `be`, `lg`, persistent: no method writes them). (N4c, 2026-10-17: the pointer and its
fields named, from the body.) -/
abbrev schema.NewAuthBackend.spec : Prop :=
  ∀ (lg : Loc) (be : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.NewAuthBackend)) (Val #lg))
      (Val #be))
  {{ (ab : GoInterface), RET #ab; ∃ l : Loc,
      ⌜ab = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty) #l⌝ ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" l ↦□ lg ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" l ↦□ be }}

end spec

end EtcdGrove
end Perennial
