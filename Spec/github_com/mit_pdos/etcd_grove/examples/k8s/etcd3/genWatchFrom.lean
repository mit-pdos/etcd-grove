/- Lean-first (no Rocq counterpart).

`genWatchFrom(n, id, c, hasC)` (watch.go; stage E of 7f-6): a watch `Gen` may return (`GenInW`),
for any random number `n` and cached object `c`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev genWatchFrom.spec : Prop :=
  ∀ (n id : w64) (c : Obj) (hasC : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genWatchFrom))
      (Val #n)) (Val #id)) (Val #c)) (Val #hasC))
  {{ (x : Input), RET #x; ⌜GenInW x⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
