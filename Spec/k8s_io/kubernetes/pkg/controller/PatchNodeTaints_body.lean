/-
`PatchNodeTaints` (`controller_utils.go:1371:6`): **a named hypothesis, gap D2** (`notes/k8s-daemonset-goose.md`): the pinned
Goose names a type of a package the file does not import through an imported package of the same
name (`pkgRef`'s substitution), so `PatchNodeTaints` is names only. The hypothesis is that it unfolds to
**its body as the translator emits it without that substitution** (`PatchNodeTaints.body`, below: the
output of the pinned translator with the substitution loop of `goose/goose.go:2979` removed, run
on ``k8s.io/kubernetes/pkg/controller`` at the pin, 2026-10-28; byte for byte its `PatchNodeTaints.impl`; nothing else in the
translation differs). So the hypothesis states what the Go code does, all of it, error paths
included, and the Perennial fix (`notes/perennial-changes.md`, "Goose: imports of packages whose
types a body names, and same-named packages") turns it into the generated `PatchNodeTaints_unfold` instance.
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
/-- go: controller_utils.go:1371:6 -/
noncomputable def PatchNodeTaints.body [GooseExts] [GoGlobalContext] : val :=
  (LamV "ctx"
  (Lam "c"
  (Lam "nodeName"
  (Lam "oldNode"
  (Lam "newNode"
  (App (Val exceptionDo)
  (Let "newNode" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "newNode"))
  (Let "oldNode" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "oldNode"))
  (Let "nodeName" (App (Val (GoInstruction (GoAlloc go.string))) (Var "nodeName"))
  (Let "c" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty))) (Var "c"))
  (Let "ctx" (App (Val (GoInstruction (GoAlloc _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "$r0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty) go!"DeepCopy"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "oldNode"))) (Val #()))
  (Let "oldNodeNoRV" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #(go!""))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)) go.any))) (Var "oldNodeNoRV"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.encoding.json.Marshal []))) (Val #())) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Let "oldDataNoRV" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.NodeSpec.ty go!"Taints"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"Spec"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "newNode")))))
  (Let "newTaints" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty) go!"DeepCopy"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "oldNode"))) (Val #()))
  (Let "newNodeClone" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (Var "newTaints"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty) go.any))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "newNodeClone")))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.encoding.json.Marshal []))) (Val #())) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "newData" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "oldDataNoRV"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "newData"))
  (Let "$a2" (App (Val (GoInstruction (Convert _root_.Perennial.k8s_io.api.core.v1.Node.ty (go.GoType.InterfaceType [])))) (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.k8s_io.api.core.v1.Node.ty))) (LiteralValue [])))
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
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Var "nodeName"))
  (Let "$a2" (Val _root_.Perennial.k8s_io.apimachinery.pkg.types.StrategicMergePatchType)
  (Let "$a3" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "patchBytes"))
  (Let "$a4" (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.PatchOptions.ty))) (LiteralValue []))
  (Let "$a5" (Val #slice.nil)
  (App (App (App (App (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.NodeInterface.ty go!"Patch"))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.CoreV1Interface.ty go!"Nodes"))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty go!"CoreV1"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty))) (Var "c"))) (Val #()))) (Val #()))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")) (Var "$a5"))))))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"failed to create patch for node %q: %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert go.string go.any))) (App (Val (GoInstruction (GoLoad go.string))) (Var "nodeName")))
  (Let "$sl1" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1")))]))))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "patchBytes") (Var "$r0")))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"failed to marshal new node %#v for node %q: %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty) go.any))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "newNodeClone")))
  (Let "$sl1" (App (Val (GoInstruction (Convert go.string go.any))) (App (Val (GoInstruction (GoLoad go.string))) (Var "nodeName")))
  (Let "$sl2" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1"))), (KeyedElement none (ElementExpression go.any (Var "$sl2")))])))))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "newData") (Var "$r0")))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (Pair (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.NodeSpec.ty go!"Taints"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"Spec"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "newNodeClone")))) (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Pair (Var "newNodeClone") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType _root_.Perennial.k8s_io.api.core.v1.Taint.ty)))) (Pair (Var "newTaints") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"failed to marshal old node %#v for node %q: %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty) go.any))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "oldNodeNoRV")))
  (Let "$sl1" (App (Val (GoInstruction (Convert go.string go.any))) (App (Val (GoInstruction (GoLoad go.string))) (Var "nodeName")))
  (Let "$sl2" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1"))), (KeyedElement none (ElementExpression go.any (Var "$sl2")))])))))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "oldDataNoRV") (Var "$r0"))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty go!"ResourceVersion"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.core.v1.Node.ty go!"ObjectMeta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Var "oldNodeNoRV")))) (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty)))) (Pair (Var "oldNodeNoRV") (Var "$r0"))))))))))))))))))

end body

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`PatchNodeTaints` unfolds to its body** (gap D2: see the file header). -/
abbrev PatchNodeTaints_body.spec : Prop :=
  FuncUnfold PatchNodeTaints [] PatchNodeTaints.body

end spec

end dsctl
end EtcdGrove
end Perennial
