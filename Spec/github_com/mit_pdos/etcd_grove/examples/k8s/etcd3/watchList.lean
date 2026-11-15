/- Lean-first (no Rocq counterpart).

`watchList()` (k8setcd3.go; k8s 7f-5, T5-c): `Set("WatchList=true")` on the default mutable feature
gate; `true` iff it returned `nil`, and then the default gate has `WatchList` on (`watchListOn`, what
the store's watch-list requests need).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev watchList.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchList)) (Val #()))
  {{ (b : Bool), RET #b; if b then watchListOn else True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
