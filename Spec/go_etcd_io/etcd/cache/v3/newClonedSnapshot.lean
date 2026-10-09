/-
`newClonedSnapshot(rev, t)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newClonedSnapshot(rev, t)`: a read-only snapshot at `rev` of the map in the (owned)
tree `t`, on a clone of it; `t` is given back. -/
abbrev newClonedSnapshot.spec : Prop :=
  ∀ (rev : w64) (t : Loc) (m : KvMap),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownBTree kvItemPtrT t kvItemIs kvLess m (DFrac.own 1) ∗ kvsAt m ∗ ⌜m.Pairwise kvLess⌝ }}
    (App (App (Val (@! newClonedSnapshot)) (Val #rev)) (Val #t))
  {{ (p : Loc), RET #p;
      ownBTree kvItemPtrT t kvItemIs kvLess m (DFrac.own 1) ∗ snapIs p (rev, m) }}

end spec

end EtcdGrove
end Perennial
