/-
Proof of `Spec/.../mvcc/watcherBatch__add.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherBatch__add
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.eventBatch__add

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

theorem mvcc.watcherBatch.add.wp_proof
    (hAdd : mvcc.eventBatch.add.spec (GF := GF) (hG := hG)) :
    mvcc.watcherBatch.add.spec (GF := GF) (hG := hG) := by
  intro wb Bm w e ev
  wp_start as ⟨HB, #He⟩
  iunfold mvcc.ownWatcherBatch at HB
  icases HB with ⟨%PB, Hm, %HBm, Hbs⟩
  wp_auto
  wp_apply wp_map_lookup1 $$ Hm as Hm
  cases hw : PB !! w with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [show (zero_val Loc) = null from rfl, _root_.decide_eq_true rfl]
    wp_auto
    wp_apply wp_mapInsert $$ Hm as Hm
    (try wp_auto)
    rw [show (zero_val eventBatch) =
      ({ evs' := slice.nil, revs' := W64 0, moreRev' := W64 0 } : eventBatch) from rfl]
    ihave Heb : mvcc.ownEventBatch «$r0_ptr» mvcc.EventBatch.empty $$ [«$r0»]
    · iunfold mvcc.ownEventBatch
      simp only [mvcc.EventBatch.empty, List.zip_nil_right]
      iexists slice.nil, []
      isplitl
      · iexact «$r0»
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      isplitl
      · ipureintro; rfl
      iapply BigSepL.bigSepL_nil.2; iempintro
    ihave %Hnn : ⌜«$r0_ptr» ≠ null⌝ $$ [Heb]
    · iunfold mvcc.ownEventBatch at Heb
      icases Heb with ⟨%s0, %ps0, Hh, -⟩
      iapply typedPointsto_not_null $$ Hh
    wp_apply (hAdd «$r0_ptr» _ e ev) $$ [$Heb $He] as Heb
    have hBw : Bm !! w = none := by rw [HBm, GMap.lookup_fmap, hw]; rfl
    rw [hBw, Option.getD_none]
    iapply HΦ
    iunfold mvcc.ownWatcherBatch
    iexists <[w := («$r0_ptr», mvcc.ebAdd mvcc.EventBatch.empty ev)]> PB
    rw [GMap.fmap_insert]
    iframe Hm
    isplitl []
    · ipureintro; rw [HBm, GMap.fmap_insert]
    iapply (BigSepM.bigSepM_insert hw).2
    iframe Hbs Heb
    ipureintro; exact Hnn
  | some p =>
    obtain ⟨eb0, B0⟩ := p
    icases BigSepM.bigSepM_insert_acc hw $$ Hbs with ⟨⟨%Hn0, HB0⟩, Hback⟩
    simp only [Option.map_some, Option.getD_some] at *
    rw [_root_.decide_eq_false Hn0]
    wp_auto
    wp_apply (hAdd eb0 _ e ev) $$ [$HB0 $He] as HB0
    have hBw : Bm !! w = some B0 := by rw [HBm, GMap.lookup_fmap, hw]; rfl
    rw [hBw, Option.getD_some]
    iapply HΦ
    iunfold mvcc.ownWatcherBatch
    iexists <[w := (eb0, mvcc.ebAdd B0 ev)]> PB
    rw [GMap.fmap_insert, GMap.insert_id _ _ _ (by rw [GMap.lookup_fmap, hw]; rfl)]
    iframe Hm
    isplitl []
    · ipureintro; rw [HBm, GMap.fmap_insert]
    iapply Hback
    iframe HB0
    ipureintro; exact Hn0

end proof

end EtcdGrove
end Perennial
