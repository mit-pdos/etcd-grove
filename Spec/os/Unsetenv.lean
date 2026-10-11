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

/-- `os.Unsetenv(k)`: some error (the environment is not modeled). -/
abbrev os.Unsetenv.spec : Prop :=
  ∀ (k : GoString),
  {{ (True : IProp GF) }}
    (App (Val #(functions _root_.Perennial.os.Unsetenv [])) (Val #k))
  {{ (e : GoInterface), RET #e; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
