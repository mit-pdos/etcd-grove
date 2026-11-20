/-
`fmt.Sprintf(format, ds, s)` of a slice of authorizer `Decision`s and a string: **the trust
boundary** (`UnconditionalPartsOrFailClosed`'s reason, `%v` of
`sets.List(d.PossibleDecisions())`). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.fmt.Base
public import Code.k8s_io.apiserver.pkg.authorization.authorizer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove


open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev fmt.SprintfDecisions.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice) (dq : DFrac) (sl : GoSlice) (ks : List w64)
    (dq' : DFrac) (x : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      args ↦*{dq} [interface.mkOk (go.GoType.SliceType
          _root_.Perennial.k8s_io.apiserver.pkg.authorization.authorizer.Decision.ty) #sl,
        interface.mkOk go.string #x] ∗ sl ↦*{dq'} ks }}
    (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args))
  {{ (s : GoString), RET #s; args ↦*{dq} [interface.mkOk (go.GoType.SliceType
          _root_.Perennial.k8s_io.apiserver.pkg.authorization.authorizer.Decision.ty) #sl,
        interface.mkOk go.string #x] ∗ sl ↦*{dq'} ks }}

end spec


end EtcdGrove
end Perennial
