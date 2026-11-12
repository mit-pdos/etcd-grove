/-
`RealPodControl.PatchPod` (`controller_utils.go:558:25`): **a named hypothesis, gap D2** (`notes/k8s-daemonset-goose.md`): the pinned
Goose names a type of a package the file does not import through an imported package of the same
name (`pkgRef`'s substitution), so `RealPodControl.PatchPod` is names only. The hypothesis is that it unfolds to
**its body as the translator emits it without that substitution** (`RealPodControl.PatchPod.body`, below: the
output of the pinned translator with the substitution loop of `goose/goose.go:2979` removed, run
on ``k8s.io/kubernetes/pkg/controller`` at the pin, 2026-10-28; byte for byte its `RealPodControl.PatchPod.impl`; nothing else in the
translation differs). So the hypothesis states what the Go code does, all of it, error paths
included, and the Perennial fix (`notes/perennial-changes.md`, "Goose: imports of packages whose
types a body names, and same-named packages") turns it into the generated `RealPodControl.TypeAssumptions.PatchPod_unfold` instance.
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
/-- go: controller_utils.go:558:25 -/
noncomputable def RealPodControl.PatchPod.body [GooseExts] [GoGlobalContext] : val :=
  (LamV "r"
  (Lam "ctx"
  (Lam "namespace"
  (Lam "name"
  (Lam "data"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "r" (App (Val (GoInstruction (GoAlloc RealPodControl.ty))) (Var "r"))
  (Let "data" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (Var "data"))
  (Let "name" (App (Val (GoInstruction (GoAlloc go.string))) (Var "name"))
  (Let "namespace" (App (Val (GoInstruction (GoAlloc go.string))) (Var "namespace"))
  (Let "ctx" (App (Val (GoInstruction (GoAlloc _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Var "name"))
  (Let "$a2" (Val _root_.Perennial.k8s_io.apimachinery.pkg.types.StrategicMergePatchType)
  (Let "$a3" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "data"))
  (Let "$a4" (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.PatchOptions.ty))) (LiteralValue []))
  (Let "$a5" (Val #slice.nil)
  (App (App (App (App (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.PodInterface.ty go!"Patch"))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "namespace"))
  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.CoreV1Interface.ty go!"Pods"))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty go!"CoreV1"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty))) (App (Val (GoInstruction (StructFieldRef RealPodControl.ty go!"KubeClient"))) (Var "r")))) (Val #()))) (Var "$a0")))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")) (Var "$a5"))))))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Let "pod" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Pod.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Pod.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.FunctionType (go.signature.Signature [(go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Pod.ty), (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.OwnerReference.ty)] false []))))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.FunctionType (go.signature.Signature [(go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Pod.ty), (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.OwnerReference.ty)] false []))))) (App (Val (GoInstruction (StructFieldRef RealPodControl.ty go!"OnWrite"))) (Var "r"))) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.FunctionType (go.signature.Signature [(go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Pod.ty), (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.OwnerReference.ty)] false []))))) (Val UntypedNil))))) (Val #false)))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Pod.ty) _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.Object.ty))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Pod.ty)))) (Var "pod")))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.GetControllerOfNoCopy []))) (Val #())) (Var "$a0")))
  (Let "ownerRef" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.OwnerReference.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.OwnerReference.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Pod.ty)))) (Var "pod"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.OwnerReference.ty)))) (Var "ownerRef"))
  (App (App (App (Val (GoInstruction (GoLoad (go.GoType.FunctionType (go.signature.Signature [(go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Pod.ty), (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.OwnerReference.ty)] false []))))) (App (Val (GoInstruction (StructFieldRef RealPodControl.ty go!"OnWrite"))) (Var "r"))) (Var "$a0")) (Var "$a1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.OwnerReference.ty)))) (Pair (Var "ownerRef") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Pod.ty)))) (Pair (Var "pod") (Var "$r0"))))))))))))))))))
  (App (Val (GoInstruction (GoLoad go.error))) (Var "$res0")))))))))

end body

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`RealPodControl.PatchPod` unfolds to its body** (gap D2: see the file header). -/
abbrev RealPodControl.PatchPod_body.spec : Prop :=
  MethodUnfold RealPodControl.ty go!"PatchPod" RealPodControl.PatchPod.body ∧
  MethodUnfold (go.GoType.PointerType RealPodControl.ty) go!"PatchPod" (LamV "$r"
    (App (Val (GoInstruction (MethodResolve RealPodControl.ty go!"PatchPod")))
      (App (Val (GoInstruction (GoLoad RealPodControl.ty))) (Var "$r"))))

end spec

end dsctl
end EtcdGrove
end Perennial
