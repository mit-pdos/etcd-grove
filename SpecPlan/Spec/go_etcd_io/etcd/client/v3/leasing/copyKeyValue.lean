/-
`copyKeyValue` (`util.go`): a fresh copy of a key-value (its value dropped if `keysOnly`).
Changes: over W0's `keyValueOwn`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.leasing.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

def copyKeyValue.spec : Prop :=
  ∀ (kv : Loc) (dq : DFrac) (m : KeyValueM) (keysOnly : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ keyValueOwn kv dq m }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.copyKeyValue)) (Val #kv)) (Val #keysOnly))
  {{ (ret : Loc), RET #ret; keyValueOwn kv dq m ∗
      keyValueOwn ret (DFrac.own 1) { m with value := if keysOnly then [] else m.value } }}

end spec

end Leasing
end EtcdGrove
end Perennial
