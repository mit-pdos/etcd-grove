module
public import GeneratedProof.go_etcd_io.bbolt

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

/-- `fmt.Sprint(a...)`: some string. `fmt` is translated names-only and Perennial models only
`Sprintf` (`Perennial/TrustedCode/fmt.lean`); like `fmt.wp_Sprintf`, this says nothing of the
string, nor asks that the arguments be formattable. -/
abbrev fmt.Sprint.spec : Prop :=
  ∀ (args : GoSlice),
  {{ (True : IProp GF) }}
    (App (Val #(functions _root_.Perennial.fmt.Sprint [])) (Val #args))
  {{ (s : GoString), RET #s; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
