/-
`DaemonSetsController.syncDaemonSet` (`daemon_controller.go:1281:34`): **a named hypothesis, gap D2** (`notes/k8s-daemonset-goose.md`): the pinned
Goose names a type of a package the file does not import through an imported package of the same
name (`pkgRef`'s substitution), so `DaemonSetsController.syncDaemonSet` is names only. The hypothesis is that it unfolds to
**its body as the translator emits it without that substitution** (`DaemonSetsController.syncDaemonSet.body`, below: the
output of the pinned translator with the substitution loop of `goose/goose.go:2979` removed, run
on ``k8s.io/kubernetes/pkg/controller/daemon`` at the pin, 2026-10-28; byte for byte its `DaemonSetsController.syncDaemonSet.impl`; nothing else in the
translation differs). So the hypothesis states what the Go code does, all of it, error paths
included, and the Perennial fix (`notes/perennial-changes.md`, "Goose: imports of packages whose
types a body names, and same-named packages") turns it into the generated `DaemonSetsController.TypeAssumptions.ptr_syncDaemonSet_unfold` instance.
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

open Iris Iris.BI k8s_io.kubernetes.pkg.controller.daemon

section body
/-- go: daemon_controller.go:1281:34 -/
noncomputable def DaemonSetsController.syncDaemonSet.body [GooseExts] [GoGlobalContext] : val :=
  (LamV "dsc"
  (Lam "ctx"
  (Lam "key"
  (App (Val wrapDefer)
  (Lam "$defer"
  (Let "dsc" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))
  (Let "key" (App (Val (GoInstruction (GoAlloc go.string))) (Var "key"))
  (Let "ctx" (App (Val (GoInstruction (GoAlloc _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.klog.v2.FromContext []))) (Val #())) (Var "$a0")))
  (Let "logger" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.klog.v2.Logger.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.klog.v2.Logger.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.utils.clock.Clock.ty go!"Now"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.utils.clock.Clock.ty))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.client_go.util.flowcontrol.Backoff.ty go!"Clock"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.client_go.util.flowcontrol.Backoff.ty)))) (App (Val (GoInstruction (StructFieldRef DaemonSetsController.ty go!"failedPodsBackoff"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))))))) (Val #()))
  (Let "startTime" (App (Val (GoInstruction (GoAlloc _root_.Perennial.time.Time.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.time.Time.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "key"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.client_go.tools.cache.SplitMetaNamespaceKey []))) (Val #())) (Var "$a0")))
  (Let "$ret0" (Fst (Fst (Var "__p")))
  (Let "$ret1" (Snd (Fst (Var "__p")))
  (Let "$ret2" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Let "name" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Let "namespace" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$v0" (App (Val (GoInstruction (GoLoad go.string))) (Var "namespace"))
  (Let "$v1" (App (Val (GoInstruction (GoLoad go.string))) (Var "name"))
  (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.k8s_io.apimachinery.pkg.types.NamespacedName.ty))) (LiteralValue [(KeyedElement (some (KeyField go!"Namespace")) (ElementExpression go.string (Var "$v0"))), (KeyedElement (some (KeyField go!"Name")) (ElementExpression go.string (Var "$v1")))]))))
  (Let "dsNamespacedName" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.apimachinery.pkg.types.NamespacedName.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.apimachinery.pkg.types.NamespacedName.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "name"))
  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.listers.apps.v1.DaemonSetNamespaceLister.ty go!"Get"))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "namespace"))
  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.listers.apps.v1.DaemonSetLister.ty go!"DaemonSets"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.listers.apps.v1.DaemonSetLister.ty))) (App (Val (GoInstruction (StructFieldRef DaemonSetsController.ty go!"dsLister"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))))) (Var "$a0")))) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ds" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.apimachinery.pkg.labels.Everything []))) (Val #())) (Val #()))
  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.listers.core.v1.NodeLister.ty go!"List"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.listers.core.v1.NodeLister.ty))) (App (Val (GoInstruction (StructFieldRef DaemonSetsController.ty go!"nodeLister"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))))) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "nodeList" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty))))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty))))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.LabelSelector.ty))) (LiteralValue []))
  (Let "everything" (App (Val (GoInstruction (GoAlloc _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.LabelSelector.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.LabelSelector.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty) (go.GoType.InterfaceType [])))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Var "ds")))
  (App (App (Val (GoInstruction (GoLoad (go.GoType.FunctionType (go.signature.Signature [(go.GoType.InterfaceType [])] false [go.string, go.error]))))) (App (Val (GoInstruction (GlobalVarAddr _root_.Perennial.k8s_io.kubernetes.pkg.controller.KeyFunc))) (Val #()))) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "dsKey" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Var "ds"))
  (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType DaemonSetsController.ty) go!"constructHistory"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))) (Var "$a0")) (Var "$a1"))))
  (Let "$ret0" (Fst (Fst (Var "__p")))
  (Let "$ret1" (Snd (Fst (Var "__p")))
  (Let "$ret2" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (Let "old" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.ControllerRevision.ty))))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.ControllerRevision.ty))))) (Val #())))
  (Let "cur" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.ControllerRevision.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.ControllerRevision.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (App (Val (map.lookup1 go.string go.string)) (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.string go.string)))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty go!"Labels"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.apps.v1.ControllerRevision.ty go!"ObjectMeta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.ControllerRevision.ty)))) (Var "cur")))))) (App (Val (GoInstruction (Convert go.untypedString go.string))) (Val _root_.Perennial.k8s_io.api.apps.v1.DefaultDaemonSetUniqueLabelKey)))
  (Let "hash" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Var "ds"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty))))) (Var "nodeList"))
  (Let "$a3" (App (Val (GoInstruction (GoLoad go.string))) (Var "hash"))
  (Let "$a4" (App (Val (GoInstruction (GoLoad go.string))) (Var "dsKey"))
  (Let "$a5" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.ControllerRevision.ty))))) (Var "old"))
  (App (App (App (App (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType DaemonSetsController.ty) go!"updateDaemonSet"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")) (Var "$a5"))))))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Var "ds"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty))))) (Var "nodeList"))
  (Let "$a3" (App (Val (GoInstruction (GoLoad go.string))) (Var "hash"))
  (Let "$a4" (Val #true)
  (App (App (App (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType DaemonSetsController.ty) go!"updateDaemonSetStatus"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")))))))
  (Let "statusErr" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))))
  (Let "$sw" (Val #true)
  (If (App (Val (GoInstruction (GoOp GoEquals go.bool))) (Pair (Var "$sw") (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "statusErr")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))) (Val #false))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad go.error))) (Var "statusErr"))
  (Let "$a1" (Val #(go!"Failed to update status"))
  (Let "$a2" (Let "$sl0" (App (Val (GoInstruction (Convert go.string go.any))) (Val #(go!"daemonSet")))
  (Let "$sl1" (App (Val (GoInstruction (Convert _root_.Perennial.k8s_io.klog.v2.ObjectRef.ty go.any))) (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty) _root_.Perennial.k8s_io.klog.v2.KMetadata.ty))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Var "ds")))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.klog.v2.KObj []))) (Val #())) (Var "$a0"))))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1")))]))))
  (App (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.github_com.go_logr.logr.Logger.ty) go!"Error"))) (Var "logger")) (Var "$a0")) (Var "$a1")) (Var "$a2")))))))
  (If (App (Val (GoInstruction (GoOp GoEquals go.bool))) (Pair (Var "$sw") (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))))))
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (If (App (Val (GoInstruction (GoOp GoEquals go.bool))) (Pair (Var "$sw") (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "statusErr")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))))))
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.error))) (Var "statusErr")))
  (App (Val doExecute)
  (Val #())))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "statusErr") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r0"))))))))
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.klog.v2.Logger.ty))) (Var "logger"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Var "dsKey"))
  (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.kubernetes.pkg.controller.ControllerExpectationsInterface.ty go!"SatisfiedExpectations"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.kubernetes.pkg.controller.ControllerExpectationsInterface.ty))) (App (Val (GoInstruction (StructFieldRef DaemonSetsController.ty go!"expectations"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))))) (Var "$a0")) (Var "$a1")))))
  (App (Val doReturn)
  (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Var "ds"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty))))) (Var "nodeList"))
  (Let "$a3" (App (Val (GoInstruction (GoLoad go.string))) (Var "hash"))
  (Let "$a4" (Val #false)
  (App (App (App (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType DaemonSetsController.ty) go!"updateDaemonSetStatus"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "hash") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"failed to construct revisions of DaemonSet: %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.ControllerRevision.ty))))) (Pair (Var "old") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.ControllerRevision.ty)))) (Pair (Var "cur") (Var "$r0"))))))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.Time.ty)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.Time.ty)))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty go!"DeletionTimestamp"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty go!"ObjectMeta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Var "ds"))))) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.Time.ty)))) (Val UntypedNil))))))
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"couldn't get key for object %#v: %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty) go.any))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Var "ds")))
  (Let "$sl1" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1")))]))))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "dsKey") (Var "$r0")))))))))))))
  (If (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.LabelSelector.ty) go.any))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.LabelSelector.ty)))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.apps.v1.DaemonSetSpec.ty go!"Selector"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty go!"Spec"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Var "ds"))))))
  (Let "$a1" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.LabelSelector.ty) go.any))) (Var "everything"))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.reflect.DeepEqual []))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty) _root_.Perennial.k8s_io.apimachinery.pkg.runtime.Object.ty))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Var "ds")))
  (Let "$a1" (Val _root_.Perennial.k8s_io.api.core.v1.EventTypeWarning)
  (Let "$a2" (App (Val (GoInstruction (Convert go.untypedString go.string))) (Val SelectingAllReason))
  (Let "$a3" (Val #(go!"This daemon set is selecting all pods. A non-empty selector is required."))
  (Let "$a4" (Val #slice.nil)
  (App (App (App (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.tools.record.EventRecorder.ty go!"Eventf"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.tools.record.EventRecorder.ty))) (App (Val (GoInstruction (StructFieldRef DaemonSetsController.ty go!"eventRecorder"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")))))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.LabelSelector.ty))) (Pair (Var "everything") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"couldn't get list of nodes when syncing daemon set %#v: %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty) go.any))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Var "ds")))
  (Let "$sl1" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1")))]))))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.Node.ty))))) (Pair (Var "nodeList") (Var "$r0")))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (Let "$a0" (Val #(go!"unable to retrieve ds %v from store: %v"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert go.string go.any))) (App (Val (GoInstruction (GoLoad go.string))) (Var "key")))
  (Let "$sl1" (App (Val (GoInstruction (Convert go.error go.any))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1")))]))))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Errorf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
  (App (Val doExecute)
  (Val #()))))))
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.apimachinery.pkg.api.errors.IsNotFound []))) (Val #())) (Var "$a0")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.types.NamespacedName.ty))) (Var "dsNamespacedName"))
  (Let "$a1" (Val #(go!""))
  (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.util.consistency.ConsistencyStore.ty go!"Clear"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.util.consistency.ConsistencyStore.ty))) (App (Val (GoInstruction (StructFieldRef DaemonSetsController.ty go!"consistencyStore"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))))) (Var "$a0")) (Var "$a1"))))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.klog.v2.Logger.ty))) (Var "logger"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Var "key"))
  (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.kubernetes.pkg.controller.ControllerExpectationsInterface.ty go!"DeleteExpectations"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.kubernetes.pkg.controller.ControllerExpectationsInterface.ty))) (App (Val (GoInstruction (StructFieldRef DaemonSetsController.ty go!"expectations"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))))) (Var "$a0")) (Var "$a1"))))))))
  (App (Val doExecute)
  (Let "$a0" (Val #(go!"Daemon set has been deleted"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert go.string go.any))) (Val #(go!"daemonset")))
  (Let "$sl1" (App (Val (GoInstruction (Convert go.string go.any))) (App (Val (GoInstruction (GoLoad go.string))) (Var "key")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1")))]))))
  (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.github_com.go_logr.logr.Logger.ty go!"Info"))) (Let "$a0" (Val #(W64 3))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.github_com.go_logr.logr.Logger.ty) go!"V"))) (Var "logger")) (Var "$a0")))) (Var "$a0")) (Var "$a1"))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.k8s_io.api.apps.v1.DaemonSet.ty)))) (Pair (Var "ds") (Var "$r0")))))))))))))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.apimachinery.pkg.types.NamespacedName.ty))) (Var "dsNamespacedName"))
  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.util.consistency.ConsistencyStore.ty go!"EnsureReady"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.util.consistency.ConsistencyStore.ty))) (App (Val (GoInstruction (StructFieldRef DaemonSetsController.ty go!"consistencyStore"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))))) (Var "$a0")))
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (Let "consistencyErr" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.client_go.util.consistency.ConsistencyError.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.k8s_io.client_go.util.consistency.ConsistencyError.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))))
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))
  (Let "$a1" (App (Val (GoInstruction (Convert (go.GoType.PointerType (go.GoType.PointerType _root_.Perennial.k8s_io.client_go.util.consistency.ConsistencyError.ty)) go.any))) (Var "consistencyErr"))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.errors.As []))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (App (Val doExecute)
  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.component_base.metrics.CounterMetric.ty go!"Inc"))) (Let "$a0" (Let "$sl0" (App (Val (GoInstruction (GoLoad go.string))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.runtime.schema.GroupResource.ty go!"Group"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.client_go.util.consistency.ConsistencyError.ty go!"GroupResource"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.client_go.util.consistency.ConsistencyError.ty)))) (Var "consistencyErr")))))
  (Let "$sl1" (App (Val (GoInstruction (GoLoad go.string))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.apimachinery.pkg.runtime.schema.GroupResource.ty go!"Resource"))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.client_go.util.consistency.ConsistencyError.ty go!"GroupResource"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.client_go.util.consistency.ConsistencyError.ty)))) (Var "consistencyErr")))))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string)))) (LiteralValue [(KeyedElement none (ElementExpression go.string (Var "$sl0"))), (KeyedElement none (ElementExpression go.string (Var "$sl1")))]))))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.k8s_io.component_base.metrics.CounterVec.ty) go!"WithLabelValues"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.component_base.metrics.CounterVec.ty)))) (App (Val (GoInstruction (GlobalVarAddr _root_.Perennial.k8s_io.kubernetes.pkg.controller.daemon.metrics.DaemonsetRequeueSkips))) (Val #())))) (Var "$a0")))) (Val #())))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r0"))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.k8s_io.apimachinery.pkg.types.NamespacedName.ty))) (Pair (Var "dsNamespacedName") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "name") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "namespace") (Var "$r0")))))))))))))))))
  (App (Val doExecute)
  (Let "$f" (Lam BAnon
  (App (Val exceptionDo)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (Let "$a0" (Val #(go!"Finished syncing daemon set"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert go.string go.any))) (Val #(go!"daemonset")))
  (Let "$sl1" (App (Val (GoInstruction (Convert go.string go.any))) (App (Val (GoInstruction (GoLoad go.string))) (Var "key")))
  (Let "$sl2" (App (Val (GoInstruction (Convert go.string go.any))) (Val #(go!"time")))
  (Let "$sl3" (App (Val (GoInstruction (Convert _root_.Perennial.time.Duration.ty go.any))) (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.time.Time.ty))) (Var "startTime"))
  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.time.Time.ty go!"Sub"))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.utils.clock.Clock.ty go!"Now"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.utils.clock.Clock.ty))) (App (Val (GoInstruction (StructFieldRef _root_.Perennial.k8s_io.client_go.util.flowcontrol.Backoff.ty go!"Clock"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.client_go.util.flowcontrol.Backoff.ty)))) (App (Val (GoInstruction (StructFieldRef DaemonSetsController.ty go!"failedPodsBackoff"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DaemonSetsController.ty)))) (Var "dsc"))))))) (Val #()))) (Var "$a0"))))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1"))), (KeyedElement none (ElementExpression go.any (Var "$sl2"))), (KeyedElement none (ElementExpression go.any (Var "$sl3")))]))))))
  (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.github_com.go_logr.logr.Logger.ty go!"Info"))) (Let "$a0" (Val #(W64 4))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.github_com.go_logr.logr.Logger.ty) go!"V"))) (Var "logger")) (Var "$a0")))) (Var "$a0")) (Var "$a1"))))))))
  (App (Val (GoInstruction (GoStore deferType))) (Pair (Var "$defer") (Let "$oldf" (App (Val (GoInstruction (GoLoad deferType))) (Var "$defer"))
  (Lam BAnon
  (Seq (App (Var "$f") (Val #()))
  (App (Var "$oldf") (Val #()))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.time.Time.ty))) (Pair (Var "startTime") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.k8s_io.klog.v2.Logger.ty))) (Pair (Var "logger") (Var "$r0")))))))))))))))

end body

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`DaemonSetsController.syncDaemonSet` unfolds to its body** (gap D2: see the file header). -/
abbrev DaemonSetsController.syncDaemonSet_body.spec : Prop :=
  MethodUnfold (go.GoType.PointerType DaemonSetsController.ty) go!"syncDaemonSet" DaemonSetsController.syncDaemonSet.body

end spec

end dsctl
end EtcdGrove
end Perennial
