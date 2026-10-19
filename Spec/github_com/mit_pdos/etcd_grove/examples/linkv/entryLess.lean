/- Lean-first (no Rocq counterpart).

`entryLess(a, b)` (linkv.go): the order `insertSorted` keeps the pending puts in, by key and then
by value (Go's `<` on strings, `GoStringLt`), as `entryLessB`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- See the file header. -/
abbrev entryLess.spec : Prop :=
  ∀ (a b : kvEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.entryLess)) (Val #a)) (Val #b))
  {{ RET #(entryLessB a b); True }}

end spec

end linkv
end EtcdGrove
end Perennial
