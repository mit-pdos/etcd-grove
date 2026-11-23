/-
`(*loggingT).output(s, logger, buf, depth, file, line, alsoToStderr)`: with no logger and a severity
`InfoLog..FatalLog`, returns. Its code is the trusted model `loggingT.output.impl`
(`TrustedCode/k8s_io/klog/v2.lean`, which says why it is faithful: Go writes the line out, to standard
error or klog's files, which no translated code reads); proved over it
(`Proof/k8s_io/klog/v2/loggingT__output.lean`). klog-printf, 2026-11-23, etcd-grove#25. Lean-first.
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
abbrev klog.loggingT.output.spec : Prop :=
  ∀ (l : Loc) (s : w32) (logger : Loc) (buf : Loc) (depth : w64) (file : GoString) (line : w64)
    (also : Bool),
  {{ (⌜logger = null ∧ (s = W32 0 ∨ s = W32 1 ∨ s = W32 2 ∨ s = W32 3)⌝ : IProp GF) }}
    (App (App (App (App (App (App (App
      (Val (l @!! go.GoType.PointerType k8s_io.klog.v2.loggingT.ty @!! go!"output"))
      (Val #s)) (Val #logger)) (Val #buf)) (Val #depth)) (Val #file)) (Val #line)) (Val #also))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
