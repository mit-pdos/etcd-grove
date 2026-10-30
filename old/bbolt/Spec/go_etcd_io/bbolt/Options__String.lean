module
public import Proof.go_etcd_io.bbolt.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `o.String()`: `"{}"` for nil options, else some string (`fmt.Sprintf`, not modelled). -/
abbrev Options.String.spec : Prop :=
  ∀ (ol : Loc) (v : Options) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ (if ol = null then True else ol ↦{dq} v) }}
    (App (Val (ol @!! go.GoType.PointerType Options.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; ⌜ol = null → s = go!"{}"⌝ ∗
      (if ol = null then True else ol ↦{dq} v) }}

end spec

end bbolt
end EtcdGrove
end Perennial
