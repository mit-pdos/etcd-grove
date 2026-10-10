/-
`errors.As(err, target)` (Go's standard library), for a target `*rpctypes.EtcdError` (a type
implementing `error`: `errors.As` does not panic). Perennial does not translate it: the trust
boundary (an axiom, `Proof/errors/As.lean`), for `client/v3/leasing`'s `acquire`. Lean-first (no
Rocq counterpart).
-/
module

public import Perennial.Proof.errors
public import Code.go_etcd_io.etcd.api.v3.v3rpc.rpctypes
public import GeneratedProof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- `errors.As(err, p)` for `p` a `*rpctypes.EtcdError` (as an `any`): some boolean; it may have
written `*p`. -/
abbrev errors.As.spec : Prop :=
  ∀ (err : GoInterface) (p : Loc) (v : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError),
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ p ↦ v }}
    (App (App (Val #(functions _root_.Perennial.errors.As [])) (Val #err))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) #p)))
  {{ (b : Bool), RET #b; ∃ v' : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError, p ↦ v' }}

end spec

end EtcdGrove
end Perennial
