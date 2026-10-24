/-
`membership.MustParseMemberIDFromKey`: the trust boundary (`membership`'s `MustParseMemberIDFromKey`
is names-only; the pure model `apply.parseMemberIDFromKey` is in `apply/RestModel.lean`).
Lean-first (no Rocq counterpart).
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

/-- `membership.MustParseMemberIDFromKey(lg, k)` when `apply.parseMemberIDFromKey k = some id`
returns `id`. -/
abbrev membership.MustParseMemberIDFromKey.spec : Prop :=
  ∀ (lg : Loc) (k : GoString) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      ⌜lg ≠ null ∧ apply.parseMemberIDFromKey k = some id⌝ }}
    (App (App (Val (@! membership.MustParseMemberIDFromKey)) (Val #lg)) (Val #k))
  {{ RET #id; True }}

end spec

end EtcdGrove
end Perennial
