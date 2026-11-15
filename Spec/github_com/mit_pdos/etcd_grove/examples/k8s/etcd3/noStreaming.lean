/- Lean-first (no Rocq counterpart).

`noStreaming()` (k8setcd3.go): `Set("EtcdRangeStream=false")` on the default mutable feature gate;
`true` iff it returned `nil`, and then the default gate has `EtcdRangeStream` off (`rangeStreamOff`,
what the store's lists need: `shouldStream` false, the paginated path).
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
abbrev noStreaming.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.noStreaming)) (Val #()))
  {{ (b : Bool), RET #b; if b then rangeStreamOff else True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
