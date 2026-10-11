/-
`store.LatestRev()`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `s.LatestRev()` (under a read lock): the latest revision of some state of the store, at
least the caller's lower bound `r0`, with a lower bound for it and its certificate `R`. -/
abbrev store.LatestRev.spec : Prop :=
  ∀ (s : Loc) (γ : StoreNames) (cap : Nat) (E : w64 → KvMap → IProp GF) (R : w64 → IProp GF) (r0 : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isStore s γ cap ∗ storeReader s γ cap E R ∗ storeRevLb γ r0 }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"LatestRev")) (Val #()))
  {{ (r : w64), RET #r; storeReader s γ cap E R ∗
      ∃ st : StoreState, storeSeen γ cap r0 st ∗ □ R st.latestRev ∗ ⌜r = st.latestRev⌝ }}

end spec

end EtcdGrove
end Perennial
