/-
`extractNodeFields` (`nodeaffinity.go:156:6`): **a named hypothesis, gap D2** (`notes/k8s-daemonset-goose.md`): the pinned
Goose names a type of a package the file does not import through an imported package of the same
name (`pkgRef`'s substitution), so `extractNodeFields` is names only. The hypothesis is that it unfolds to
**its body as the translator emits it without that substitution** (`extractNodeFields.body`, below: the
output of the pinned translator with the substitution loop of `goose/goose.go:2979` removed, run
on ``k8s.io/component-helpers/scheduling/corev1/nodeaffinity`` at the pin, 2026-10-28; byte for byte its `extractNodeFields.impl`; nothing else in the
translation differs). So the hypothesis states what the Go code does, all of it, error paths
included, and the Perennial fix (`notes/perennial-changes.md`, "Goose: imports of packages whose
types a body names, and same-named packages") turns it into the generated `extractNodeFields_unfold` instance.
`?` in `etc/link-lean-first-k8sdaemon.txt`: a hypothesis of every result that reaches it.
-/
module

public import Proof.k8s_io.kubernetes.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI k8s_io.component_helpers.scheduling.corev1.nodeaffinity

section body
/-- go: nodeaffinity.go:156:6 -/
noncomputable def extractNodeFields.body [GooseExts] [GoGlobalContext] : val :=
  (LamV "n"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "n" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "n"))
  (Let "$r0" (App (App (Val (GoInstruction (FuncResolve go.make1 [_root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty]))) (Val #())) (Val #()))
  (Let "f" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Var "f"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Pair (Var "$res0") (Var "$r0"))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty go!"Name"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"ObjectMeta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "n")))))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))) (Val #(W64 0)))))
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty go!"Name"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"ObjectMeta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "n")))))
  (App (Val doExecute)
  (App (App (App (Val (map.insert go.string)) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Var "f"))) (Val #(go!"metadata.name"))) (Var "$r0"))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Pair (Var "f") (Var "$r0")))))))))
  (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Var "$res0")))))

end body

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`extractNodeFields` unfolds to its body** (gap D2: see the file header). -/
abbrev extractNodeFields_body.spec : Prop :=
  FuncUnfold extractNodeFields [] extractNodeFields.body

end spec

end dsctl
end EtcdGrove
end Perennial
