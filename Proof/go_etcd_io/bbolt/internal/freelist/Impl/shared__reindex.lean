/-
`shared.reindex()` (U2 internal): the cache rebuilt from the free ids (obtained back
through the interface, `freePageIds`) and the pending ids.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.reindex()`: the cache becomes exactly the free and pending ids. -/
abbrev shared.reindex.spec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (fl : FLPg) (c : GMap w64 Unit), fl.WFw →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownShC s I.iface fl c ∗ I.own fl.free }}
    (App (Val #(methods (go.GoType.PointerType shared.ty)
      go!"go.etcd.io/bbolt/internal/freelist.reindex" #s)) (Val #()))
  {{ RET #(); ownShW s I.iface fl ∗ I.own fl.free }}

theorem shared.reindex.wp_proof (I : FLImpl (GF := GF)) (hF : I.FreePageIdsSpec) :
    shared.reindex.spec I := by
  sorry

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
