/-
`Assert`'s spec (`internal/common/verify.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace common

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `Assert(cond, msg, v...)` returns when `cond` holds; with a false condition it panics (through
`fmt.Sprintf`), which the spec excludes by taking the argument `true`. -/
abbrev Assert.spec : Prop :=
  ∀ (msg : GoString) (vs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (App (App (Val #(functions Assert [])) (Val #true)) (Val #msg)) (Val #vs))
  {{ RET #(); True }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
