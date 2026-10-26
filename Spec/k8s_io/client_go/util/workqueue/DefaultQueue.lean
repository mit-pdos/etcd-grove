/-
`DefaultQueue[T]()` (`queue.go`): a new, empty slice FIFO, as a `Queue[T]`. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI k8s_io.client_go.util.workqueue

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `DefaultQueue[T]()`: a `*queue[T]` holding nothing. -/
abbrev DefaultQueue.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T],
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
    (App (Val #(functions DefaultQueue [T])) (Val #()))
  {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType (queue.ty T)) #l : Queue K);
      ownFifo (GF := GF) (K := K) l [] }}

end spec

end workqueue
end EtcdGrove
end Perennial
