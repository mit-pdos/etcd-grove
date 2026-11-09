/-
`closeAll` (`util.go`): closes each waiter channel (each once: its close right).
Changes: over `waitCloser` (was `waitcClose`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

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

def closeAll.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (cs : List GoChan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ sl ↦*{dq} cs ∗ [∗list] c ∈ cs, waitCloser c }}
    (App (Val (@! go_etcd_io.etcd.client.v3.leasing.closeAll)) (Val #sl))
  {{ RET #(); sl ↦*{dq} cs }}

end spec

end Leasing
end EtcdGrove
end Perennial
