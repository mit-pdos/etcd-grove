/-
`ComputeHash` (`controller_utils.go:1402:6`): **a named hypothesis, gap D2** (`notes/k8s-daemonset-goose.md`): the pinned
Goose names a type of a package the file does not import through an imported package of the same
name (`pkgRef`'s substitution), so `ComputeHash` is names only. The hypothesis is that it unfolds to
**its body as the translator emits it without that substitution** (`ComputeHash.body`, below: the
output of the pinned translator with the substitution loop of `goose/goose.go:2979` removed, run
on ``k8s.io/kubernetes/pkg/controller`` at the pin, 2026-10-28; byte for byte its `ComputeHash.impl`; nothing else in the
translation differs). So the hypothesis states what the Go code does, all of it, error paths
included, and the Perennial fix (`notes/perennial-changes.md`, "Goose: imports of packages whose
types a body names, and same-named packages") turns it into the generated `ComputeHash_unfold` instance.
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
/-- go: controller_utils.go:1402:6 -/
noncomputable def ComputeHash.body [GooseExts] [GoGlobalContext] : val :=
  (LamV "template"
  (Lam "collisionCount"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "collisionCount" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType go.int32)))) (Var "collisionCount"))
  (Let "template" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.PodTemplateSpec.ty)))) (Var "template"))
  (Let "$r0" (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.hash.fnv.New32a []))) (Val #())) (Val #()))
  (Let "podTemplateSpecHasher" (App (Val (GoInstruction (GoAlloc _root_.Perennial.hash.Hash32.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.hash.Hash32.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (Let "$a0" (Let "$sl0" (App (Val (GoInstruction (Convert go.uint32 go.any))) (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.hash.Hash32.ty go!"Sum32"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.hash.Hash32.ty))) (Var "podTemplateSpecHasher"))) (Val #())))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0")))])))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Sprint []))) (Val #())) (Var "$a0")))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.apimachinery.pkg.util.rand.SafeEncodeString []))) (Val #())) (Var "$a0")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.PointerType go.int32)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.PointerType go.int32)))) (Var "collisionCount")) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.PointerType go.int32)))) (Val UntypedNil))))))
  (Let "$r0" (App (App (Val (GoInstruction (FuncResolve go.make2 [(go.GoType.SliceType go.byte)]))) (Val #())) (Val #(W64 8)))
  (Let "collisionCountBytes" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "collisionCountBytes"))
  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.hash.Hash32.ty go!"Write"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.hash.Hash32.ty))) (Var "podTemplateSpecHasher"))) (Var "$a0"))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "collisionCountBytes"))
  (Let "$a1" (App (Val (GoInstruction (Convert go.int32 go.uint32))) (App (Val (GoInstruction (GoLoad go.int32))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType go.int32)))) (Var "collisionCount"))))
  (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.encoding.binary.littleEndian.ty) go!"PutUint32"))) (App (Val (GoInstruction (GlobalVarAddr _root_.Perennial.encoding.binary.LittleEndian))) (Val #()))) (Var "$a0")) (Var "$a1"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "collisionCountBytes") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (Convert _root_.Perennial.hash.Hash32.ty _root_.Perennial.hash.Hash.ty))) (App (Val (GoInstruction (GoLoad _root_.Perennial.hash.Hash32.ty))) (Var "podTemplateSpecHasher")))
  (Let "$a1" (App (Val (GoInstruction (Convert _root_.Perennial.k8s_io.api.core.v1.PodTemplateSpec.ty (go.GoType.InterfaceType [])))) (App (Val (GoInstruction (GoLoad _root_.Perennial.k8s_io.api.core.v1.PodTemplateSpec.ty))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.k8s_io.api.core.v1.PodTemplateSpec.ty)))) (Var "template"))))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.k8s_io.kubernetes.pkg.util.hash.DeepHashObject []))) (Val #())) (Var "$a0")) (Var "$a1"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.hash.Hash32.ty))) (Pair (Var "podTemplateSpecHasher") (Var "$r0"))))))))))
  (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0"))))))

end body

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`ComputeHash` unfolds to its body** (gap D2: see the file header). -/
abbrev ComputeHash_body.spec : Prop :=
  FuncUnfold ComputeHash [] ComputeHash.body

end spec

end dsctl
end EtcdGrove
end Perennial
