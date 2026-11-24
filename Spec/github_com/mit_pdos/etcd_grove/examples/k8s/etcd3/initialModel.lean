/- Lean-first (no Rocq counterpart).

`initialModel(st0)` (`realcheck.go`, TestCorrectness's `NewModelFromStorage` of the seeded store): a new, owned
`*correctness.Model` of the store's abstraction `absR st` (its items at their store keys, its resource version, the
prefix `/registry`, the keys whose stored data is not canonical). The store's keys are distinct (`Go`'s map
insertions keep the last binding, `GMap.ofList` the first), and at most `2^62` (`itemsRO`'s bound).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealMS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (mstore)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev initialModel.spec : Prop :=
  ∀ (s0 : mstore) (st : GSt), (st.items.map fun it => storeKeyL it.key').Nodup →
  st.items.length ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      storeOwn s0 st }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialModel)) (Val #s0))
  {{ (mp : Loc), RET #mp; modelOwn mp (absR st) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
