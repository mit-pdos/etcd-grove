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

/-- `p.Get()`: a value of the pool. -/
abbrev sync.Pool.Get.spec : Prop :=
  ∀ (p : Loc) (P : GoInterface → IProp GF),
  {{ isPool p P }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sync.Pool.ty @!! go!"Get")) (Val #()))
  {{ (v : GoInterface), RET #v; P v }}

end spec

end bbolt
end EtcdGrove
end Perennial
