/-
`store.Restore(kvs, rev)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
import EtcdGrove.Cache.InvStore

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

/-- `s.Restore(kvs, rev)`, by the writer: the store's state becomes `restoreState rev kvs`
(the latest map built from `kvs`, the latest revision `rev`, the history that one
snapshot). `rev` must not be below the latest revision (the lower bounds readers hold
stay true; the cache restores from a newer `Get`). -/
abbrev store.Restore.spec : Prop :=
  ∀ (s : Loc) (γ : StoreNames) (cap : Nat) (st : StoreState) (kvsSl : GoSlice) (kvs : KvMap)
    (dq : DFrac) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isStore s γ cap ∗ storeWriter s γ cap st ∗ kvsSl ↦*{dq} (kvs.map Prod.snd) ∗ kvsAt kvs ∗
      ⌜sint.Z st.latestRev ≤ sint.Z rev⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Restore")) (Val #kvsSl)) (Val #rev))
  {{ RET #(); kvsSl ↦*{dq} (kvs.map Prod.snd) ∗ storeWriter s γ cap (restoreState rev kvs) ∗
      storeRevLb γ rev }}

end spec

end EtcdGrove
end Perennial
