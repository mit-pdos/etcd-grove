module
public import Proof.sync.PoolModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `p.Put(v)`: the pool takes a value. -/
abbrev sync.Pool.Put.spec : Prop :=
  ∀ (p : Loc) (P : GoInterface → IProp GF) (v : GoInterface),
  {{ isPool p P ∗ P v }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sync.Pool.ty @!! go!"Put")) (Val #v))
  {{ RET #(); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
