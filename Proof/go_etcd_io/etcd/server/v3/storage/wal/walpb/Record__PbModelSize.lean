/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/walpb/Record__PbModelSize.lean`: cached, the
size cache is loaded from the record's invariant (`recHidden`, the cache mode `Any`) and, if above 0,
returned less one; otherwise each set field adds its tag (one byte) and value
(`pbcodec.SizeVarint`, a `bytes` field's length too), then the unknown fields' length: `recSize`,
field by field; the cache is stored into the invariant.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__PbModelSize
public import Net.Spec.models_lab.pbcodec.SizeVarint
public import Perennial.Spec.sync.atomic.LoadInt32
public import Perennial.Spec.sync.atomic.StoreInt32

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]
variable [models_lab.pbcodec.Assumptions]

set_option goose.wp.extras true

theorem go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.PbModelSize.wp_proof
    (wp_SizeVarint : models_lab.pbcodec.SizeVarint.spec (GF := GF) (hG := hG))
    (wp_LoadInt32 : sync.atomic.LoadInt32.spec (GF := GF) (hG := hG))
    (wp_StoreInt32 : sync.atomic.StoreInt32.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.PbModelSize.spec (GF := GF) (hG := hG) := by
  intro l c cached hsz
  wp_start as #Hro
  iunfold recRoC at Hro
  iunfold recPtsCC at Hro
  icases Hro with ⟨%pt, %pc, %ds, %Hl, #HT, #HTc, #HC, #HCc, #HD, #HDc, #Hhid⟩
  iunfold recHidden at Hhid
  icases Hhid with ⟨#Hinv, ⟨%us, #HU, #HUs⟩, %Huf⟩
  cases cached
  all_goals (wp_auto; simp only [decide_eq_false Hl]; wp_auto)
  rotate_left
  -- cached: the size cache, from the invariant
  wp_apply (wp_LoadInt32 _ (DFrac.own 1))
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%st, %sc, Hst, Hsc⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(nroot.@"protobuf") from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  inext
  iexists sc
  iframe Hsc
  iintro Hsc
  imod Hclose2 with -
  imod Hclose $$ [Hst Hsc] with -
  · inext; iexists st, sc; iframe
  imodintro
  wp_auto
  wp_if_destruct
  all_goals first
    | (iapply HΦ; ipureintro; intro h; cases h)
    | skip
  -- the size, field by field (both the uncached call and a cached one whose cache is 0)
  all_goals rcases c with ⟨_ | t, _ | k, _ | d, u⟩
  all_goals simp only at Huf hsz ⊢
  all_goals (iunfold recCell at HTc; simp only)
  all_goals first
    | (icases HTc with %Hpt; subst Hpt; wp_auto)
    | (ihave %Hpt := typedPointsto_not_null pt _ _ $$ HTc
       simp only [decide_eq_false Hpt, Bool.not_false]
       wp_auto
       wp_apply wp_SizeVarint)
  all_goals (iunfold recCell at HCc; simp only)
  all_goals first
    | (icases HCc with %Hpc; subst Hpc; wp_auto)
    | (ihave %Hpc := typedPointsto_not_null pc _ _ $$ HCc
       simp only [decide_eq_false Hpc, Bool.not_false]
       wp_auto
       wp_apply wp_SizeVarint)
  all_goals (iunfold recBytes at HDc; simp only)
  all_goals first
    | (icases HDc with %Hds; subst Hds; wp_auto)
    | (icases HDc with ⟨%Hds, #Hd⟩
       ihave %Hdl := ownSlice_len _ _ _ $$ Hd
       simp only [decide_eq_false Hds, Bool.not_false]
       wp_auto
       wp_apply wp_SizeVarint)
  all_goals ihave %Hul := ownSlice_len _ _ _ $$ HUs
  -- the cache stored (into the invariant), the size returned
  all_goals wp_if_destruct
  all_goals
    wp_apply (wp_StoreInt32 _ _)
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%st, %sc, Hst, Hsc⟩
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(nroot.@"protobuf") from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    inext
    iexists sc
    iframe Hsc
    iintro Hsc
    imod Hclose2 with -
    imod Hclose $$ [Hst Hsc] with -
    · inext; iexists st, _; iframe
    imodintro
    wp_auto
    iapply HΦ
    ipureintro
    intro _
  all_goals
    try clear Hif
    simp only [recSize, models_lab.pbcodec.zext32] at hsz ⊢
    rw [models_lab.pbcodec.w64OfNat us.len u.length (models_lab.pbcodec.uintOfSint _ _ Hul)]
    try rw [models_lab.pbcodec.uintOfSint ds.len d.length Hdl]
    try rw [models_lab.pbcodec.w64OfNat ds.len d.length (models_lab.pbcodec.uintOfSint _ _ Hdl)]
    simp only [W64, ← BitVec.ofInt_add]
    rw [← W64, models_lab.pbcodec.sintW64 _ (by omega) (by omega)]
    omega

end proof

end EtcdGrove
end Perennial
