/-
`AddOrUpdateLabelsOnNode` (`controller_utils.go:1416:6`): **a named hypothesis, gap D2** (`notes/k8s-daemonset-goose.md`): the pinned
Goose names a type of a package the file does not import through an imported package of the same
name (`pkgRef`'s substitution), so `AddOrUpdateLabelsOnNode` is names only. The hypothesis is that it unfolds to
**its body as the translator emits it without that substitution** (`AddOrUpdateLabelsOnNode.body`, below: the
output of the pinned translator with the substitution loop of `goose/goose.go:2979` removed, run
on ``k8s.io/kubernetes/pkg/controller`` at the pin, 2026-10-28; byte for byte its `AddOrUpdateLabelsOnNode.impl`; nothing else in the
translation differs). So the hypothesis states what the Go code does, all of it, error paths
included, and the Perennial fix (`notes/perennial-changes.md`, "Goose: imports of packages whose
types a body names, and same-named packages") turns it into the generated `AddOrUpdateLabelsOnNode_unfold` instance.
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
/-- go: controller_utils.go:1416:6 -/
noncomputable def AddOrUpdateLabelsOnNode.body [FfiSyntax] [GoGlobalContext] : val :=
  (LamV "kubeClient"
  (Lam "nodeName"
  (Lam "labelsToUpdate"
  (App (Val exceptionDo)
  (Let "labelsToUpdate" (App (Val (GoInstruction (GoAlloc (go.GoType.MapType go.string go.string)))) (Var "labelsToUpdate"))
  (Let "nodeName" (App (Val (GoInstruction (GoAlloc go.string))) (Var "nodeName"))
  (Let "kubeClient" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty))) (Var "kubeClient"))
  (Let "$r0" (Val #true)
  (Let "firstTry" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.util.wait.Backoff.ty))) (App (Val (GoInstruction (GlobalVarAddr UpdateLabelBackoff))) (Val #())))
  (Let "$a1" (Lam BAnon
  (App (Val exceptionDo)
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Let "node" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Val #())))
  (Let "$r0" (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.GetOptions.ty))) (LiteralValue []))
  (Let "option" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.GetOptions.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.GetOptions.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.context.TODO []))) (Val #())) (Val #()))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Var "nodeName"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.GetOptions.ty))) (Var "option"))
  (App (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.NodeInterface.ty go!"Get"))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.CoreV1Interface.ty go!"Nodes"))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty go!"CoreV1"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty))) (Var "kubeClient"))) (Val #()))) (Val #()))) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty) go!"DeepCopy"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node"))) (Val #()))
  (Let "newNode" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty) go.any))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node")))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.encoding.json.Marshal []))) (Val #())) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "oldData" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty) go.any))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "newNode")))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.encoding.json.Marshal []))) (Val #())) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "newData" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "oldData"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "newData"))
  (Let "$a2" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty) (go.GoType.InterfaceType [])))) (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.api.core.v1.Node.ty))) (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.k8s_io.api.core.v1.Node.ty))) (LiteralValue []))))
  (Let "$a3" (Val #slice.nil)
  (App (App (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.apimachinery.pkg.util.strategicpatch.CreateTwoWayMergePatch []))) (Val #())) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3"))))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "patchBytes" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))))
  (Let "__p" (Let "$a0" (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.context.TODO []))) (Val #())) (Val #()))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty go!"Name"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"ObjectMeta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node")))))
  (Let "$a2" (Val _root_.Perennial.k8s_io.apimachinery.pkg.types.StrategicMergePatchType)
  (Let "$a3" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "patchBytes"))
  (Let "$a4" (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.PatchOptions.ty))) (LiteralValue []))
  (Let "$a5" (Val #slice.nil)
  (App (App (App (App (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.NodeInterface.ty go!"Patch"))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.CoreV1Interface.ty go!"Nodes"))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty go!"CoreV1"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty))) (Var "kubeClient"))) (Val #()))) (Val #()))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")) (Var "$a5"))))))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"failed to patch the node: %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"failed to create a two-way merge patch: %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "patchBytes") (Var "$r0")))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"failed to marshal the new node %#v: %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty) go.any))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "newNode")))
  (Let "$sl1" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1")))]))))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "newData") (Var "$r0")))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"failed to marshal the existing node %#v: %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty) go.any))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "node")))
  (Let "$sl1" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1")))]))))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "oldData") (Var "$r0")))))))))))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.string go.string)))) (Var "labelsToUpdate"))
  (Let "value" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Let "key" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val (map.forRange go.string go.string)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "value"))
  (App (Val doExecute)
  (App (App (App (Val (map.insert go.string)) (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.string go.string)))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty go!"Labels"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"ObjectMeta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "newNode")))))) (App (Val (GoInstruction (GoLoad go.string))) (Var "key"))) (Var "$r0"))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "key") (Var "$key")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "value") (Var "$value"))))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.MapType go.string go.string)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.string go.string)))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty go!"Labels"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"ObjectMeta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "newNode"))))) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.MapType go.string go.string)))) (Val UntypedNil)))))
  (Let "$r0" (App (App (Val (GoInstruction (FuncResolve go.make1 [(go.GoType.MapType go.string go.string)]))) (Val #())) (Val #()))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.MapType go.string go.string)))) (Pair (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty go!"Labels"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"ObjectMeta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "newNode")))) (Var "$r0")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Pair (Var "newNode") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Pair (Var "node") (Var "$r0"))))))))))))
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
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "firstTry") (Var "$r0"))))))))))))))

end body

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`AddOrUpdateLabelsOnNode` unfolds to its body** (gap D2: see the file header). -/
abbrev AddOrUpdateLabelsOnNode_body.spec : Prop :=
  FuncUnfold AddOrUpdateLabelsOnNode [] AddOrUpdateLabelsOnNode.body

end spec

end dsctl
end EtcdGrove
end Perennial
