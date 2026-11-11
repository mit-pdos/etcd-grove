/-
`channelContext.Deadline()` (`k8s.io/apimachinery/pkg/util/wait`, `wait.go:141`; translated): no
deadline (premise-fixes-8, C1: grpc's transport calls `Deadline()` on every call's context, finding
N1 of the Scope). Lean-first.
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.wait.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `channelContext{stopCh: sc}.Deadline()` returns the zero time and `false` (no deadline). -/
abbrev wait.channelContext.Deadline.spec : Prop :=
  ∀ (sc : GoChan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait }}
    (App (Val (k8s_io.apimachinery.pkg.util.wait.channelContext.mk sc @!!
      k8s_io.apimachinery.pkg.util.wait.channelContext.ty @!! go!"Deadline")) (Val #()))
  {{ (t : _root_.Perennial.time.Time), RET (PairV #t #false); True }}

end spec

end EtcdGrove
end Perennial
