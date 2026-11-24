/-
`logging.printWithInfos(buf, file, line, s, logger, filter, depth, args...)` (klog v2.140.0,
`klog.go:742-758`), on klog's global `logging`, with no logger and no filter, for the one argument
`printS` passes (`klog.go:851`): a `*bytes.Buffer` at `lb` holding `bs`. `fmt.Fprint` prints it
(its `String()`) into `buf`, a newline is appended unless it ends in one, and `output` is called.
Proved over its translated body (`Proof/k8s_io/klog/v2/loggingT__printWithInfos.lean`; klog-infos,
2026-11-23, etcd-grove#25). Lean-first (no Rocq counterpart).
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
abbrev klog.loggingT.printWithInfos.spec : Prop :=
  ∀ (buf : Loc) (hdr : List w8) (file : GoString) (line : w64) (s : w32) (logger : Loc)
    (filter : GoInterface) (depth : w64) (args : GoSlice) (dq : DFrac) (lb : Loc) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗
      ⌜logger = null ∧ filter = interface.nil ∧ (s = W32 0 ∨ s = W32 1 ∨ s = W32 2 ∨ s = W32 3)⌝ ∗
      _root_.Perennial.bytes.ownBuffer
        (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" buf) hdr ∗
      args ↦*{dq} [interface.mkOk (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) #lb] ∗
      _root_.Perennial.bytes.ownBuffer lb bs }}
    (App (App (App (App (App (App (App (App
      (Val (globalAddr k8s_io.klog.v2.logging @!! go.GoType.PointerType k8s_io.klog.v2.loggingT.ty
        @!! go!"printWithInfos"))
      (Val #buf)) (Val #file)) (Val #line)) (Val #s)) (Val #logger)) (Val #filter)) (Val #depth))
      (Val #args))
  {{ RET #(); args ↦*{dq} [interface.mkOk (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) #lb] ∗
      _root_.Perennial.bytes.ownBuffer lb bs }}

end spec

end EtcdGrove
end Perennial
