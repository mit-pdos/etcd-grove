/- Lean-first (no Rocq counterpart).

`storeHash(st)` (export.go): a hash of the store `st`; some `w64` (`mix`'s header).
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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev storeHash.spec : Prop :=
  ∀ (st : mstore) (s : GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ storeOwn st s }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeHash)) (Val #st))
  {{ (x : w64), RET #x; True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
