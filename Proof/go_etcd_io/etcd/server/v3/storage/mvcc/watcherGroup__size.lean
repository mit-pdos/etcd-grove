/-
Proof of `Spec/.../mvcc/watcherGroup__size.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__size

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watcherGroup.size.wp_proof : mvcc.watcherGroup.size.spec (GF := GF) (hG := hG) := by
  intro wg W q
  wp_start as Hg
  iunfold mvcc.ownWatcherGroup at Hg
  icases Hg with ⟨%km, %ws, %t, %KM, %L, Hg⟩
  iNamed Hg
  iunfold mvcc.ownWatcherSet at Hws
  ihave %Hgnn := typedPointsto_not_null _ _ _ $$ Hwg
  icases typedPointsto_split _ _ _ $$ Hwg with Hwg
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hwg
  wp_auto
  wp_apply wp_map_len_lt $$ Hws as ⟨Hws, %Hlt⟩
  ihave Hwg : typedPointsto wg (watcherGroup.mk km (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #t) ws) (DFrac.own q) $$ [keyWatchers ranges watchers]
  · iapply typedPointsto_combine _ _ _ Hgnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  have hs : GMap.size (domSet W) = GMap.size W := GMap.map_size_fmap _ _
  rw [hs] at Hlt ⊢
  iapply HΦ
  isplitl
  · iunfold mvcc.ownWatcherGroup
    iexists km, ws, t, KM, L
    simp only [named]
    iframe Hwg Hkm Hivt Hranges Hfixed
    isplitl
    · iunfold mvcc.ownWatcherSet; iexact Hws
    ipureintro; exact HL
  ipureintro; exact Hlt

end proof

end EtcdGrove
end Perennial
