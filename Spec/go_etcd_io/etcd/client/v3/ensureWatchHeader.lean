/-
`clientv3.ensureWatchHeader(hdr)` (`client/v3/watch.go`). **Users**: `dispatchEvent`.
**Proof sketch**: a `nil` header becomes a fresh zero one (`protoRest_zero`). **Changes**:
restated over `respHeaderOwn`. **Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiWatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `ensureWatchHeader(hdr)`: the header, or a fresh zero one for `nil`. -/
def ensureWatchHeader.spec : Prop :=
  ∀ (hdr : Loc) (dq : DFrac) (h : Option HeaderM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optOwn respHeaderOwn hdr dq h }}
    (App (Val (@! go_etcd_io.etcd.client.v3.ensureWatchHeader)) (Val #hdr))
  {{ (r : Loc), RET #r; match h with
      | some m => iprop(⌜r = hdr⌝ ∗ respHeaderOwn hdr dq m)
      | none => respHeaderOwn r (DFrac.own 1) HeaderM.zero }}

end spec

end ClientV3
end EtcdGrove
end Perennial
