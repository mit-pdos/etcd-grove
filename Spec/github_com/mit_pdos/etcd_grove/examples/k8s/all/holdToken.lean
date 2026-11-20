/-
`holdToken()` (`examples/k8s/all/all.go`; `notes/k8s-unified-scope.md`): sleeps forever.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_all

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]

/-- `holdToken()` does not return (`False` after it): the goroutine `Main` runs it on holds no
resource and never ends, so `Main` keeps the token `wp_fork_tok_self` gives it, for the store's
goroutine to exit with (as `k8s_etcd3.holdToken.spec`). -/
abbrev holdToken.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.all }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.all.holdToken)) (Val #()))
  {{ RET #(); False }}

end spec

end k8s_all
end EtcdGrove
end Perennial
