/-
`LazyErrorNodeSelector.Match` (`nodeaffinity.go:84:34`): **a named hypothesis, gap D2** (`notes/k8s-daemonset-goose.md`): the pinned
Goose names a type of a package the file does not import through an imported package of the same
name (`pkgRef`'s substitution), so `LazyErrorNodeSelector.Match` is names only. The hypothesis is that it unfolds to
**its body as the translator emits it without that substitution** (`LazyErrorNodeSelector.Match.body`, below: the
output of the pinned translator with the substitution loop of `goose/goose.go:2979` removed, run
on ``k8s.io/component-helpers/scheduling/corev1/nodeaffinity`` at the pin, 2026-10-28; byte for byte its `LazyErrorNodeSelector.Match.impl`; nothing else in the
translation differs). So the hypothesis states what the Go code does, all of it, error paths
included, and the Perennial fix (`notes/perennial-changes.md`, "Goose: imports of packages whose
types a body names, and same-named packages") turns it into the generated `LazyErrorNodeSelector.TypeAssumptions.ptr_Match_unfold` instance.
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
/-- go: nodeaffinity.go:84:34 -/
noncomputable def LazyErrorNodeSelector.Match.body [GooseExts] [GoGlobalContext] : val :=
  (LamV "ns"
  (Lam "node"
  (App (Val exceptionDo)
  (Let "ns" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType LazyErrorNodeSelector.ty)))) (Var "ns"))
  (Let "node" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.string go.string)))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty go!"Labels"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"ObjectMeta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node")))))
  (Let "nodeLabels" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.apimachinery.pkg.labels.Set'.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.apimachinery.pkg.labels.Set'.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node"))
  (App (App (Val (GoInstruction (FuncResolve extractNodeFields []))) (Val #())) (Var "$a0")))
  (Let "nodeFields" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "errs" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.error)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.error)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Pair (Val #false) (App (Val (GoInstruction (Convert _root_.Perennial.k8s_io.apimachinery.pkg.util.errors.Aggregate.ty go.error))) (Let "$a0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.error)))) (Var "errs"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.apimachinery.pkg.util.errors.NewAggregate []))) (Val #())) (Var "$a0")))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.apimachinery.pkg.util.errors.Flatten []))) (Val #())) (Var "$a0"))))))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType nodeSelectorTerm.ty)))) (App (Val (GoInstruction (StructFieldRef LazyErrorNodeSelector.ty go!"terms"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType LazyErrorNodeSelector.ty)))) (Var "ns"))))
  (App (App (Val (slice.forRange nodeSelectorTerm.ty)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (Let "term" (App (Val (GoInstruction (GoAlloc nodeSelectorTerm.ty))) (Var "$value"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.labels.Set'.ty))) (Var "nodeLabels"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Var "nodeFields"))
  (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType nodeSelectorTerm.ty) go!"match"))) (Var "term")) (Var "$a0")) (Var "$a1"))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "tErrs" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.error)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.error)))) (Val #())))
  (Let "match" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "match"))
  (App (Val doReturn)
  (Pair (Val #true) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))
  (App (Val doExecute)
  (Val #())))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.error)))) (Var "tErrs"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.error)]))) (Val #())) (Var "$a0"))) (Val #(W64 0)))))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.error)))) (Var "errs"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.error)))) (Var "tErrs"))
  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType go.error)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doContinue) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.error)))) (Pair (Var "errs") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.error)))) (Pair (Var "tErrs") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "match") (Var "$r0"))))))))))))))
  (App (Val doExecute)
  (Var "$key"))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Pair (Var "nodeFields") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.k8s_io.apimachinery.pkg.labels.Set'.ty))) (Pair (Var "nodeLabels") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node")) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Val UntypedNil)))))
  (App (Val doReturn)
  (Pair (Val #false) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))
  (App (Val doExecute)
  (Val #())))))))))

end body

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`LazyErrorNodeSelector.Match` unfolds to its body** (gap D2: see the file header). -/
abbrev LazyErrorNodeSelector.Match_body.spec : Prop :=
  MethodUnfold (go.GoType.PointerType LazyErrorNodeSelector.ty) go!"Match" LazyErrorNodeSelector.Match.body

end spec

end dsctl
end EtcdGrove
end Perennial
