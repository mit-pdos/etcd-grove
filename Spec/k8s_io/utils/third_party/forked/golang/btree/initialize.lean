module
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI k8s_io.utils.third_party.forked.golang.btree

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- The package's `initialize'`: initialize its imports (`cmp`, `sort`, `sync`); it has no
globals of its own. -/
abbrev initialize.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.k8s_io.utils.third_party.forked.golang.btree get_is_pkg_init →
  {{ ownInitializing get_is_pkg_init }}
    (App (Val initialize') (Val #()))
  {{ RET #(); ownInitializing get_is_pkg_init ∗
      isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree }}

end spec

end btree
end EtcdGrove
end Perennial
