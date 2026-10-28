/-
`RealPodControl.DeletePod` (`controller_utils.go:619:25`): **a named hypothesis, gap D2** (`notes/k8s-daemonset-goose.md`): the pinned
Goose names a type of a package the file does not import through an imported package of the same
name (`pkgRef`'s substitution), so `RealPodControl.DeletePod` is names only. The hypothesis is that it unfolds to
**its body as the translator emits it without that substitution** (`RealPodControl.DeletePod.body`, below: the
output of the pinned translator with the substitution loop of `goose/goose.go:2979` removed, run
on ``k8s.io/kubernetes/pkg/controller`` at the pin, 2026-10-28; byte for byte its `RealPodControl.DeletePod.impl`; nothing else in the
translation differs). So the hypothesis states what the Go code does, all of it, error paths
included, and the Perennial fix (`notes/perennial-changes.md`, "Goose: imports of packages whose
types a body names, and same-named packages") turns it into the generated `RealPodControl.TypeAssumptions.DeletePod_unfold` instance.
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
/-- go: controller_utils.go:619:25 -/
noncomputable def RealPodControl.DeletePod.body [GooseExts] [GoGlobalContext] : val :=
  (LamV "r"
  (Lam "ctx"
  (Lam "namespace"
  (Lam "podID"
  (Lam "object"
  (App (Val exceptionDo)
  (Let "r" (App (Val (GoInstruction (GoAlloc RealPodControl.ty))) (Var "r"))
  (Let "object" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.apimachinery.pkg.runtime.Object.ty))) (Var "object"))
  (Let "podID" (App (Val (GoInstruction (GoAlloc go.string))) (Var "podID"))
  (Let "namespace" (App (Val (GoInstruction (GoAlloc go.string))) (Var "namespace"))
  (Let "ctx" (App (Val (GoInstruction (GoAlloc _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (Convert _root_.Perennial.k8s_io.apimachinery.pkg.runtime.Object.ty (go.GoType.InterfaceType [])))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.runtime.Object.ty))) (Var "object")))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.apimachinery.pkg.api.«meta».Accessor []))) (Val #())) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Let "accessor" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.Object.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.Object.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.klog.v2.FromContext []))) (Val #())) (Var "$a0")))
  (Let "logger" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.klog.v2.Logger.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.klog.v2.Logger.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.runtime.Object.ty))) (Var "object"))
  (Let "$a1" (Val _root_.Perennial.k8s_io.api.core.v1.EventTypeNormal)
  (Let "$a2" (App (Val (GoInstruction (Convert go.untypedString go.string))) (Val SuccessfulDeletePodReason))
  (Let "$a3" (Val #(go!"Deleted pod: %v"))
  (Let "$a4" (Let "$sl0" (App (Val (GoInstruction (Convert go.string (go.GoType.InterfaceType [])))) (App (Val (GoInstruction (GoLoad go.string))) (Var "podID")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.InterfaceType []))))) (LiteralValue [(KeyedElement none (ElementExpression (go.GoType.InterfaceType []) (Var "$sl0")))])))
  (App (App (App (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.tools.record.EventRecorder.ty go!"Eventf"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.tools.record.EventRecorder.ty))) (App (Val (GoInstruction (StructFieldRef RealPodControl.ty go!"Recorder"))) (Var "r")))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")))))))))))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Var "podID"))
  (Let "$a2" (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.DeleteOptions.ty))) (LiteralValue []))
  (App (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.PodInterface.ty go!"Delete"))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "namespace"))
  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.CoreV1Interface.ty go!"Pods"))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty go!"CoreV1"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty))) (App (Val (GoInstruction (StructFieldRef RealPodControl.ty go!"KubeClient"))) (Var "r")))) (Val #()))) (Var "$a0")))) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"unable to delete pods: %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.runtime.Object.ty))) (Var "object"))
  (Let "$a1" (Val _root_.Perennial.k8s_io.api.core.v1.EventTypeWarning)
  (Let "$a2" (App (Val (GoInstruction (Convert go.untypedString go.string))) (Val FailedDeletePodReason))
  (Let "$a3" (Val #(go!"Error deleting: %v"))
  (Let "$a4" (Let "$sl0" (App (Val (GoInstruction (Convert go.error (go.GoType.InterfaceType [])))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.InterfaceType []))))) (LiteralValue [(KeyedElement none (ElementExpression (go.GoType.InterfaceType []) (Var "$sl0")))])))
  (App (App (App (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.tools.record.EventRecorder.ty go!"Eventf"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.tools.record.EventRecorder.ty))) (App (Val (GoInstruction (StructFieldRef RealPodControl.ty go!"Recorder"))) (Var "r")))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")))))))))))
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.apimachinery.pkg.api.errors.IsNotFound []))) (Val #())) (Var "$a0")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))))
  (App (Val doExecute)
  (Let "$a0" (Val #(go!"Pod has already been deleted."))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert go.string go.any))) (Val #(go!"pod")))
  (Let "$sl1" (App (Val (GoInstruction (Convert _root_.Perennial.k8s_io.klog.v2.ObjectRef.ty go.any))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "namespace"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Var "podID"))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.klog.v2.KRef []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1")))]))))
  (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.github_com.go_logr.logr.Logger.ty go!"Info"))) (Let "$a0" (Val #(W64 4))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.github_com.go_logr.logr.Logger.ty) go!"V"))) (Var "logger")) (Var "$a0")))) (Var "$a0")) (Var "$a1"))))))
  (App (Val doExecute)
  (Val #()))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r0"))))))))))
  (App (Val doExecute)
  (Let "$a0" (Val #(go!"Deleting pod"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert go.string go.any))) (Val #(go!"controller")))
  (Let "$sl1" (App (Val (GoInstruction (Convert go.string go.any))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.Object.ty go!"GetName"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.Object.ty))) (Var "accessor"))) (Val #())))
  (Let "$sl2" (App (Val (GoInstruction (Convert go.string go.any))) (Val #(go!"pod")))
  (Let "$sl3" (App (Val (GoInstruction (Convert _root_.Perennial.k8s_io.klog.v2.ObjectRef.ty go.any))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "namespace"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Var "podID"))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.klog.v2.KRef []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1"))), (KeyedElement none (ElementExpression go.any (Var "$sl2"))), (KeyedElement none (ElementExpression go.any (Var "$sl3")))]))))))
  (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.github_com.go_logr.logr.Logger.ty go!"Info"))) (Let "$a0" (Val #(W64 2))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.github_com.go_logr.logr.Logger.ty) go!"V"))) (Var "logger")) (Var "$a0")))) (Var "$a0")) (Var "$a1"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.k8s_io.klog.v2.Logger.ty))) (Pair (Var "logger") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"object does not have ObjectMeta, %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.Object.ty))) (Pair (Var "accessor") (Var "$r0")))))))))))))))))))))))

end body

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`RealPodControl.DeletePod` unfolds to its body** (gap D2: see the file header). -/
abbrev RealPodControl.DeletePod_body.spec : Prop :=
  MethodUnfold RealPodControl.ty go!"DeletePod" RealPodControl.DeletePod.body ∧
  MethodUnfold (go.GoType.PointerType RealPodControl.ty) go!"DeletePod" (LamV "$r"
    (App (Val (GoInstruction (MethodResolve RealPodControl.ty go!"DeletePod")))
      (App (Val (GoInstruction (GoLoad RealPodControl.ty))) (Var "$r"))))

end spec

end dsctl
end EtcdGrove
end Perennial
