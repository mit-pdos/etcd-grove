/-
`(*progressRequest).toPB()`: a progress request. Users: `run`.
Internal (`WatchInternal.lean`'s vocabulary). **Changes** from `specs-ref`'s file of the same
name: restated over this branch's vocabulary (the old `isWGS`, `WEnv`, `watchSrvFacts` gone).
**Margin**: mirrors the code.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WatchInternal

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

/-- `pr.toPB()`: a fresh progress request. -/
def progressRequest.toPB.spec : Prop :=
  ∀ (pr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (pr @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.progressRequest.ty @!! go!"toPB")) (Val #()))
  {{ (p : Loc), RET #p; watchReqOwn p (DFrac.own 1) .progress }}

end spec

end ClientV3
end EtcdGrove
end Perennial
