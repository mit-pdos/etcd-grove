/-
`PreferredSchedulingTerms.Score` (`nodeaffinity.go:139:36`): **a named hypothesis, gap D2** (`notes/k8s-daemonset-goose.md`): the pinned
Goose names a type of a package the file does not import through an imported package of the same
name (`pkgRef`'s substitution), so `PreferredSchedulingTerms.Score` is names only. The hypothesis is that it unfolds to
**its body as the translator emits it without that substitution** (`PreferredSchedulingTerms.Score.body`, below: the
output of the pinned translator with the substitution loop of `goose/goose.go:2979` removed, run
on ``k8s.io/component-helpers/scheduling/corev1/nodeaffinity`` at the pin, 2026-10-28; byte for byte its `PreferredSchedulingTerms.Score.impl`; nothing else in the
translation differs). So the hypothesis states what the Go code does, all of it, error paths
included, and the Perennial fix (`notes/perennial-changes.md`, "Goose: imports of packages whose
types a body names, and same-named packages") turns it into the generated `PreferredSchedulingTerms.TypeAssumptions.ptr_Score_unfold` instance.
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
/-- go: nodeaffinity.go:139:36 -/
noncomputable def PreferredSchedulingTerms.Score.body [GooseExts] [GoGlobalContext] : val :=
  (LamV "t"
  (Lam "node"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.int64))) (App (Val (GoInstruction (GoZeroVal go.int64))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "t" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType PreferredSchedulingTerms.ty)))) (Var "t"))
  (Let "node" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node"))
  (Let "score" (App (Val (GoInstruction (GoAlloc go.int64))) (App (Val (GoInstruction (GoZeroVal go.int64))) (Val #())))
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.string go.string)))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty go!"Labels"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"ObjectMeta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node")))))
  (Let "nodeLabels" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.apimachinery.pkg.labels.Set'.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.apimachinery.pkg.labels.Set'.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node"))
  (App (App (Val (GoInstruction (FuncResolve extractNodeFields []))) (Val #())) (Var "$a0")))
  (Let "nodeFields" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int64))) (Var "score"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType preferredSchedulingTerm.ty)))) (App (Val (GoInstruction (StructFieldRef PreferredSchedulingTerms.ty go!"terms"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType PreferredSchedulingTerms.ty)))) (Var "t"))))
  (App (App (Val (slice.forRange preferredSchedulingTerm.ty)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (Let "term" (App (Val (GoInstruction (GoAlloc preferredSchedulingTerm.ty))) (Var "$value"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.labels.Set'.ty))) (Var "nodeLabels"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Var "nodeFields"))
  (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType preferredSchedulingTerm.ty) go!"match"))) (Var "term")) (Var "$a0")) (Var "$a1"))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "score") (App (Val (GoInstruction (GoOp GoPlus go.int64))) (Pair (App (Val (GoInstruction (GoLoad go.int64))) (Var "score")) (App (Val (GoInstruction (Convert go.int go.int64))) (App (Val (GoInstruction (GoLoad go.int))) (App (Val (GoInstruction (StructFieldRef preferredSchedulingTerm.ty go!"weight"))) (Var "term")))))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (Var "$r1")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r0")))))))))))))
  (App (Val doExecute)
  (Var "$key")))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.k8s_io.apimachinery.pkg.fields.Set'.ty))) (Pair (Var "nodeFields") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.k8s_io.apimachinery.pkg.labels.Set'.ty))) (Pair (Var "nodeLabels") (Var "$r0")))))))))))
  (App (Val (GoInstruction (GoLoad go.int64))) (Var "$res0"))))))

end body

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`PreferredSchedulingTerms.Score` unfolds to its body** (gap D2: see the file header). -/
abbrev PreferredSchedulingTerms.Score_body.spec : Prop :=
  MethodUnfold (go.GoType.PointerType PreferredSchedulingTerms.ty) go!"Score" PreferredSchedulingTerms.Score.body

end spec

end dsctl
end EtcdGrove
end Perennial
