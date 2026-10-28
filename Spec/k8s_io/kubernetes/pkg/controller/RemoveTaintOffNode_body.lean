/-
`RemoveTaintOffNode` (`controller_utils.go:1317:6`): **a named hypothesis, gap D2** (`notes/k8s-daemonset-goose.md`): the pinned
Goose names a type of a package the file does not import through an imported package of the same
name (`pkgRef`'s substitution), so `RemoveTaintOffNode` is names only. The hypothesis is that it unfolds to
**its body as the translator emits it without that substitution** (`RemoveTaintOffNode.body`, below: the
output of the pinned translator with the substitution loop of `goose/goose.go:2979` removed, run
on ``k8s.io/kubernetes/pkg/controller`` at the pin, 2026-10-28; byte for byte its `RemoveTaintOffNode.impl`; nothing else in the
translation differs). So the hypothesis states what the Go code does, all of it, error paths
included, and the Perennial fix (`notes/perennial-changes.md`, "Goose: imports of packages whose
types a body names, and same-named packages") turns it into the generated `RemoveTaintOffNode_unfold` instance.
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

open Iris Iris.BI k8s_io.kubernetes.pkg.controller

section body
/-- go: controller_utils.go:1317:6 -/
noncomputable def RemoveTaintOffNode.body [FfiSyntax] [GoGlobalContext] : val :=
  (LamV "ctx"
  (Lam "c"
  (Lam "nodeName"
  (Lam "node"
  (Lam "taints"
  (App (Val exceptionDo)
  (Let "taints" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty))))) (Var "taints"))
  (Let "node" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node"))
  (Let "nodeName" (App (Val (GoInstruction (GoAlloc go.string))) (Var "nodeName"))
  (Let "c" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty))) (Var "c"))
  (Let "ctx" (App (Val (GoInstruction (GoAlloc _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #true)
  (Let "firstTry" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.util.wait.Backoff.ty))) (App (Val (GoInstruction (GlobalVarAddr UpdateTaintBackoff))) (Val #())))
  (Let "$a1" (Lam BAnon
  (App (Val exceptionDo)
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Let "oldNode" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Val #())))
  (Let "$r0" (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.GetOptions.ty))) (LiteralValue []))
  (Let "option" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.GetOptions.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.GetOptions.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Var "nodeName"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.GetOptions.ty))) (Var "option"))
  (App (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.NodeInterface.ty go!"Get"))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.CoreV1Interface.ty go!"Nodes"))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty go!"CoreV1"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty))) (Var "c"))) (Val #()))) (Val #()))) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "newNode" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Val #())))
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "oldNode"))
  (Let "oldNodeCopy" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #false)
  (Let "updated" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty))) (Var "c"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad go.string))) (Var "nodeName"))
  (Let "$a3" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "oldNode"))
  (Let "$a4" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "newNode"))
  (App (App (App (App (App (App (Val (GoInstruction (FuncResolve PatchNodeTaints []))) (Val #())) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4"))))))))))
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "updated")))
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))
  (App (Val doExecute)
  (Val #()))))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty))))) (Var "taints"))
  (Let "taint" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (Val #())))
  (App (App (Val (slice.forRange (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty))) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "oldNodeCopy"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (Var "taint"))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.kubernetes.pkg.util.taints.RemoveTaint []))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (Let "$ret0" (Fst (Fst (Var "__p")))
  (Let "$ret1" (Snd (Fst (Var "__p")))
  (Let "$ret2" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "curNewNode" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "updated")) (Val #true) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "curNewNode"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "curNewNode"))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Pair (Var "oldNodeCopy") (Var "$r0")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Pair (Var "newNode") (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "updated") (Var "$r0"))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"failed to remove taint of node"))
  (Let "$a1" (Val #slice.nil)
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Pair (Var "curNewNode") (Var "$r0")))))))))))))))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (Pair (Var "taint") (Var "$value")))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "updated") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Pair (Var "oldNodeCopy") (Var "$r0"))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Pair (Var "oldNode") (Var "$r0"))))))))))))
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "firstTry"))
  (Let "$r0" (Val #(go!"0"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #false)
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "firstTry") (Var "$r0")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.GetOptions.ty go!"ResourceVersion"))) (Var "option")) (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.GetOptions.ty))) (Pair (Var "option") (Var "$r0")))))))))))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.client_go.util.retry.RetryOnConflict []))) (Val #())) (Var "$a0")) (Var "$a1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "firstTry") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node")) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Val UntypedNil))))))
  (Let "$r0" (Val #false)
  (Let "match" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "match")))
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))
  (App (Val doExecute)
  (Val #())))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty))))) (Var "taints"))
  (Let "taint" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (Val #())))
  (App (App (Val (slice.forRange (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty))) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.NodeSpec.ty go!"Taints"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"Spec"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node")))))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (Var "taint"))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.kubernetes.pkg.util.taints.TaintExists []))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (Let "$r0" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doBreak) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "match") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (Pair (Var "taint") (Var "$value")))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "match") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty))))) (Var "taints"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Taint.ty))]))) (Val #())) (Var "$a0"))) (Val #(W64 0)))))
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))
  (App (Val doExecute)
  (Val #())))))))))))))))

end body

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`RemoveTaintOffNode` unfolds to its body** (gap D2: see the file header). -/
abbrev RemoveTaintOffNode_body.spec : Prop :=
  FuncUnfold RemoveTaintOffNode [] RemoveTaintOffNode.body

end spec

end dsctl
end EtcdGrove
end Perennial
