/-
`RealRSControl.PatchReplicaSet` (`controller_utils.go:443:24`): **a named hypothesis, gap D2** (`notes/k8s-daemonset-goose.md`): the pinned
Goose names a type of a package the file does not import through an imported package of the same
name (`pkgRef`'s substitution), so `RealRSControl.PatchReplicaSet` is names only. The hypothesis is that it unfolds to
**its body as the translator emits it without that substitution** (`RealRSControl.PatchReplicaSet.body`, below: the
output of the pinned translator with the substitution loop of `goose/goose.go:2979` removed, run
on ``k8s.io/kubernetes/pkg/controller`` at the pin, 2026-10-28; byte for byte its `RealRSControl.PatchReplicaSet.impl`; nothing else in the
translation differs). So the hypothesis states what the Go code does, all of it, error paths
included, and the Perennial fix (`notes/perennial-changes.md`, "Goose: imports of packages whose
types a body names, and same-named packages") turns it into the generated `RealRSControl.TypeAssumptions.PatchReplicaSet_unfold` instance.
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
/-- go: controller_utils.go:443:24 -/
noncomputable def RealRSControl.PatchReplicaSet.body [FfiSyntax] [GoGlobalContext] : val :=
  (LamV "r"
  (Lam "ctx"
  (Lam "namespace"
  (Lam "name"
  (Lam "data"
  (App (Val exceptionDo)
  (Let "r" (App (Val (GoInstruction (GoAlloc RealRSControl.ty))) (Var "r"))
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
  (App (App (App (App (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.apps.v1.ReplicaSetInterface.ty go!"Patch"))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "namespace"))
  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.typed.apps.v1.AppsV1Interface.ty go!"ReplicaSets"))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty go!"AppsV1"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.client_go.kubernetes.Interface.ty))) (App (Val (GoInstruction (StructFieldRef RealRSControl.ty go!"KubeClient"))) (Var "r")))) (Val #()))) (Var "$a0")))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")) (Var "$a5"))))))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))))))))))

end body

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`RealRSControl.PatchReplicaSet` unfolds to its body** (gap D2: see the file header). -/
abbrev RealRSControl.PatchReplicaSet_body.spec : Prop :=
  MethodUnfold RealRSControl.ty go!"PatchReplicaSet" RealRSControl.PatchReplicaSet.body ∧
  MethodUnfold (go.GoType.PointerType RealRSControl.ty) go!"PatchReplicaSet" (LamV "$r"
    (App (Val (GoInstruction (MethodResolve RealRSControl.ty go!"PatchReplicaSet")))
      (App (Val (GoInstruction (GoLoad RealRSControl.ty))) (Var "$r"))))

end spec

end dsctl
end EtcdGrove
end Perennial
