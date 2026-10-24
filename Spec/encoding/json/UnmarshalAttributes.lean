/-
`json.Unmarshal` of a `*membership.Attributes`: the trust boundary (`encoding/json` is names-only;
the pure model `apply.jsonDecodeAttributes` is in `apply/RestModel.lean`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `json.Unmarshal(bs_sl, &attributes)` when `apply.jsonDecodeAttributes s = some (name, urls)`
returns `nil` and populates `attributes` with `Name' := name` and a read-only slice
`urls_sl ↦*□ urls`. -/
abbrev json.UnmarshalAttributes.spec : Prop :=
  ∀ (bs_sl : GoSlice) (s : GoString) (dq : DFrac) (attr_ptr : Loc)
    (a0 : membership.Attributes) (name : GoString) (urls : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗
      bs_sl ↦*{dq} s ∗ attr_ptr ↦ a0 ∗
      ⌜apply.jsonDecodeAttributes s = some (name, urls)⌝ }}
    (App (App (Val (@! _root_.Perennial.encoding.json.Unmarshal)) (Val #bs_sl))
      (Val #(interface.mkOk (go.GoType.PointerType membership.Attributes.ty) #attr_ptr)))
  {{ RET #(GoInterface.nil);
      bs_sl ↦*{dq} s ∗
      ∃ urls_sl : GoSlice,
        attr_ptr ↦ ({ Name' := name, ClientURLs' := urls_sl } : membership.Attributes) ∗
        urls_sl ↦*□ urls }}

end spec

end EtcdGrove
end Perennial
