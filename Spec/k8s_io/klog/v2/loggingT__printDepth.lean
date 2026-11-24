/-
`logging.printDepth(s, logger, filter, depth, args...)` (klog v2.140.0, `klog.go:733-740`), on klog's
global `logging`, with no logger and no filter, for the one argument `printS` passes
(`klog.go:851`): a `*bytes.Buffer` at `lb` holding `bs`. `header`, then `printWithInfos`. Proved over
its translated body (`Proof/k8s_io/klog/v2/loggingT__printDepth.lean`; klog-infos, 2026-11-23,
etcd-grove#25). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

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

/-- See the file header. -/
abbrev klog.loggingT.printDepth.spec : Prop :=
  ∀ (s : w32) (logger : Loc) (filter : GoInterface) (depth : w64) (args : GoSlice) (dq : DFrac)
    (lb : Loc) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗
      ⌜logger = null ∧ filter = interface.nil ∧ (s = W32 0 ∨ s = W32 1 ∨ s = W32 2 ∨ s = W32 3)⌝ ∗
      args ↦*{dq} [interface.mkOk (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) #lb] ∗
      _root_.Perennial.bytes.ownBuffer lb bs }}
    (App (App (App (App (App
      (Val (globalAddr k8s_io.klog.v2.logging @!! go.GoType.PointerType k8s_io.klog.v2.loggingT.ty
        @!! go!"printDepth"))
      (Val #s)) (Val #logger)) (Val #filter)) (Val #depth)) (Val #args))
  {{ RET #(); args ↦*{dq} [interface.mkOk (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) #lb] ∗
      _root_.Perennial.bytes.ownBuffer lb bs }}

end spec

end EtcdGrove
end Perennial
