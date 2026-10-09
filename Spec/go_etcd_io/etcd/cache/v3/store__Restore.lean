/-
`store.Restore(kvs, rev)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `s.Restore(kvs, rev)`, by any writer (`isStoreWriter`): under the write lock, the store's
state becomes `restoreState rev kvs` (the latest map built from `kvs`, the latest revision `rev`,
the history that one snapshot), whatever state it was in. `rev` must not be below that state's
latest revision (the lower bounds readers hold stay true): the caller holds some `P` with which no
revision the store can be at (`R`, the latest revision's certificate, which the lock invariant
keeps of it) is above `rev`; it certifies the new snapshot (`E rev (restoreMap kvs)`) and the new
revision (`R rev`). Afterwards the latest revision and the newest snapshot are at least `rev`. -/
abbrev store.Restore.spec : Prop :=
  ∀ (s : Loc) (γ : StoreNames) (cap : Nat) (E : w64 → KvMap → IProp GF) (R : w64 → IProp GF)
    (P : IProp GF) (kvsSl : GoSlice) (kvs : KvMap) (dq : DFrac) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isStore s γ cap ∗ isStoreWriter s γ cap E R ∗ kvsSl ↦*{dq} (kvs.map Prod.snd) ∗ kvsAt kvs ∗
      P ∗ ⌜∀ r, (P ∗ R r ⊢ ⌜sint.Z r ≤ sint.Z rev⌝)⌝ ∗ □ E rev (restoreMap kvs) ∗ □ R rev }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Restore")) (Val #kvsSl)) (Val #rev))
  {{ RET #(); kvsSl ↦*{dq} (kvs.map Prod.snd) ∗ P ∗ storeRevLb γ rev ∗ storeSnapLb γ rev }}

end spec

end EtcdGrove
end Perennial
