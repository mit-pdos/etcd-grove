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

/-- `os.Exit(code)`: the program ends; the call never returns (hence the postcondition
`False`). The model has no process exit, so this is the trust boundary's statement of it: no code
after the call runs. -/
abbrev os.Exit.spec : Prop :=
  ∀ (code : w64),
  {{ (True : IProp GF) }}
    (App (Val #(functions _root_.Perennial.os.Exit [])) (Val #code))
  {{ RET #(); False }}

end spec

end bbolt
end EtcdGrove
end Perennial
