import EtcdGrove.Btree.Defs
import EtcdGrove.Btree.Model
import EtcdGrove.Btree.Init
import EtcdGrove.Btree.Item

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI github_com.google.btree

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

/-- `Int.Less(b)`: `a < b.(Int)` (the type assertion panics unless `b` holds an `Int`). -/
abbrev Int.Less.spec : Prop :=
  ∀ (a kb : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree }}
    (App (Val (a @!! Int'.ty @!! go!"Less")) (Val #(interface.mkOk Int'.ty #kb)))
  {{ RET #(decide (sint.Z a < sint.Z kb)); True }}

end spec

end Btree
end EtcdGrove
end Perennial
