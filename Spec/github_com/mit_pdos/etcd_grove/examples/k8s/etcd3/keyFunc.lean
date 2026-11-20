/- Lean-first (no Rocq counterpart).

`keyFunc(obj)` (`realcheck.go`, the checker's key of an object): for the driver's `*Obj` `o`
(read-only, `deepRep DFrac.discard x (.obj o)`), its store key `storeKey(o.Namespace + "/" + o.Name)`
and no error. Only `*Obj`s are specified: the validator calls it on the driver's watch events, whose
objects are `*Obj`s on the paths it accepts (k8s 7g step 5).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev keyFunc.spec : Prop :=
  ∀ (x : GoInterface) (o : Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      deepRep DFrac.discard x (.obj o) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.keyFunc)) (Val #x))
  {{ RET (PairV #(storeKeyL (o.Namespace' ++ go!"/" ++ o.Name')) #GoInterface.nil); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
