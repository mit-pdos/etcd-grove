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

/-- `os.Getenv(k)`: some string (the environment is not modeled: any value it may hold). -/
abbrev os.Getenv.spec : Prop :=
  ∀ (k : GoString),
  {{ (True : IProp GF) }}
    (App (Val #(functions _root_.Perennial.os.Getenv [])) (Val #k))
  {{ (s : GoString), RET #s; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
