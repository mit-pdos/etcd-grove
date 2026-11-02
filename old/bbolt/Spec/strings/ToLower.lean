module
public import Proof.go_etcd_io.bbolt.internal.common.Init

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
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `strings.ToLower(s)`: some string (its value is not modeled; bbolt compares it with
constants only to decide whether to run its optional checks). -/
abbrev strings.ToLower.spec : Prop :=
  ∀ (s : GoString),
  {{ (True : IProp GF) }}
    (App (Val #(functions _root_.Perennial.strings.ToLower [])) (Val #s))
  {{ (t : GoString), RET #t; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
