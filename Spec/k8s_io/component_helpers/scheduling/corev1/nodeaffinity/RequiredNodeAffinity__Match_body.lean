/-
`RequiredNodeAffinity.Match` (`nodeaffinity.go:331:31`): **a named hypothesis, gap D2** (`notes/k8s-daemonset-goose.md`): the pinned
Goose names a type of a package the file does not import through an imported package of the same
name (`pkgRef`'s substitution), so `RequiredNodeAffinity.Match` is names only. The hypothesis is that it unfolds to
**its body as the translator emits it without that substitution** (`RequiredNodeAffinity.Match.body`, below: the
output of the pinned translator with the substitution loop of `goose/goose.go:2979` removed, run
on ``k8s.io/component-helpers/scheduling/corev1/nodeaffinity`` at the pin, 2026-10-28; byte for byte its `RequiredNodeAffinity.Match.impl`; nothing else in the
translation differs). So the hypothesis states what the Go code does, all of it, error paths
included, and the Perennial fix (`notes/perennial-changes.md`, "Goose: imports of packages whose
types a body names, and same-named packages") turns it into the generated `RequiredNodeAffinity.TypeAssumptions.Match_unfold` instance.
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
/-- go: nodeaffinity.go:331:31 -/
noncomputable def RequiredNodeAffinity.Match.body [GooseExts] [GoGlobalContext] : val :=
  (LamV "s"
  (Lam "node"
  (App (Val exceptionDo)
  (Let "s" (App (Val (GoInstruction (GoAlloc RequiredNodeAffinity.ty))) (Var "s"))
  (Let "node" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Pair (Val #true) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.PointerType LazyErrorNodeSelector.ty)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.PointerType LazyErrorNodeSelector.ty)))) (App (Val (GoInstruction (StructFieldRef RequiredNodeAffinity.ty go!"nodeSelector"))) (Var "s"))) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.PointerType LazyErrorNodeSelector.ty)))) (Val UntypedNil))))))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node"))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType LazyErrorNodeSelector.ty) go!"Match"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType LazyErrorNodeSelector.ty)))) (App (Val (GoInstruction (StructFieldRef RequiredNodeAffinity.ty go!"nodeSelector"))) (Var "s")))) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (App (Val doReturn)
  (Pair (Var "$ret0") (Var "$ret1"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals _root_.Perennial.k8s_io.apimachinery.pkg.labels.Selector.ty))) (Pair (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.labels.Selector.ty))) (App (Val (GoInstruction (StructFieldRef RequiredNodeAffinity.ty go!"labelSelector"))) (Var "s"))) (App (Val (GoInstruction (Convert go.untypedNil _root_.Perennial.k8s_io.apimachinery.pkg.labels.Selector.ty))) (Val UntypedNil))))))
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (Let "$a0" (App (Val (GoInstruction (Convert _root_.Perennial.k8s_io.apimachinery.pkg.labels.Set'.ty _root_.Perennial.k8s_io.apimachinery.pkg.labels.Labels.ty))) (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.string go.string)))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty go!"Labels"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"ObjectMeta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node"))))))
  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.apimachinery.pkg.labels.Selector.ty go!"Matches"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.labels.Selector.ty))) (App (Val (GoInstruction (StructFieldRef RequiredNodeAffinity.ty go!"labelSelector"))) (Var "s")))) (Var "$a0"))))
  (App (Val doReturn)
  (Pair (Val #false) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))
  (App (Val doExecute)
  (Val #())))
  (App (Val doExecute)
  (Val #())))))))))

end body

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`RequiredNodeAffinity.Match` unfolds to its body** (gap D2: see the file header). -/
abbrev RequiredNodeAffinity.Match_body.spec : Prop :=
  MethodUnfold RequiredNodeAffinity.ty go!"Match" RequiredNodeAffinity.Match.body ∧
  MethodUnfold (go.GoType.PointerType RequiredNodeAffinity.ty) go!"Match" (LamV "$r"
    (App (Val (GoInstruction (MethodResolve RequiredNodeAffinity.ty go!"Match")))
      (App (Val (GoInstruction (GoLoad RequiredNodeAffinity.ty))) (Var "$r"))))

end spec

end dsctl
end EtcdGrove
end Perennial
