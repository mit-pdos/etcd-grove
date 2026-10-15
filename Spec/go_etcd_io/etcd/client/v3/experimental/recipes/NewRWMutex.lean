/-
`recipes.NewRWMutex(s, prefix)` (`client/v3/experimental/recipes/rwmutex.go`). Lean-first (no Rocq counterpart);
see `InvRWMutex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRWMutex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`NewRWMutex(s, prefix)`**, for a session `s` (of `client`, with the lease `id`) whose client
has the recipes' contracts at `prefix ++ "/"`: the mutex on `prefix ++ "/"` (its context
`context.TODO()`), with no key (`myKey` nil). -/
abbrev NewRWMutex.spec : Prop :=
  ∀ (s : Loc) (γ : concurrency.SessionNames) (client : Loc) (id : w64) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ concurrency.isSession s γ client id ∗
      isEtcdRecipesClient client (pfx ++ go!"/") ∗ context.isClosedchanInit }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.NewRWMutex)) (Val #s))
      (Val #pfx))
  {{ (m : Loc), RET #m; isRWMutex m s γ client id (pfx ++ go!"/") ∗ rwMyKey m (pfx ++ go!"/") none }}

end spec

end recipes
end EtcdGrove
end Perennial
