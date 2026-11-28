/- Lean-first (no Rocq counterpart).

`mix(h, v)` (export.go): a step of the FNV-1a hash. Only its type matters: no spec relies on a
hash value (hash-consing and the configuration set compare what a bucket holds).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (mstore mcfg hnode Input histHashes cfgSet)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev mix.spec : Prop :=
  ∀ (h v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.mix)) (Val #h)) (Val #v))
  {{ (x : w64), RET #x; True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
