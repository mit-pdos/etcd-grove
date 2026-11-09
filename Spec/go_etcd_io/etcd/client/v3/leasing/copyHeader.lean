/-
`copyHeader` (`util.go`): a fresh copy (`nil` of `nil`). Changes: over W0's `respHeaderOwn`.
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

def copyHeader.spec : Prop :=
  ∀ (hdr : Loc) (dq : DFrac) (hm : Option HeaderM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ optOwn respHeaderOwn hdr dq hm }}
    (App (Val (@! go_etcd_io.etcd.client.v3.leasing.copyHeader)) (Val #hdr))
  {{ (ret : Loc), RET #ret; optOwn respHeaderOwn hdr dq hm ∗ optOwn respHeaderOwn ret (DFrac.own 1) hm }}

end spec

end Leasing
end EtcdGrove
end Perennial
