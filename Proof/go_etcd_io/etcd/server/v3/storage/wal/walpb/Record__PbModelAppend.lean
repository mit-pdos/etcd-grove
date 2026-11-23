/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/walpb/Record__PbModelAppend.lean`: each set
field is a tag then its value (`pbcodec.AppendTag`, `AppendVarint`, `AppendBytes`), then the unknown
fields are appended as they are; the bytes are `recEnc`'s, field by field (`WalPbWire.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__PbModelAppend
public import Net.Spec.models_lab.pbcodec.AppendTag
public import Net.Spec.models_lab.pbcodec.AppendVarint
public import Net.Spec.models_lab.pbcodec.AppendBytes

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

theorem go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.PbModelAppend.wp_proof
    (wp_AppendTag : models_lab.pbcodec.AppendTag.spec (GF := GF) (hG := hG))
    (wp_AppendVarint : models_lab.pbcodec.AppendVarint.spec (GF := GF) (hG := hG))
    (wp_AppendBytes : models_lab.pbcodec.AppendBytes.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.PbModelAppend.spec (GF := GF) (hG := hG) := by
  intro l c b bs cached
  wp_start as ⟨#Hro, Hb, Hcap⟩
  iunfold recRoC at Hro
  iunfold recPtsCC at Hro
  icases Hro with ⟨%pt, %pc, %ds, %Hl, #HT, #HTc, #HC, #HCc, #HD, #HDc, #Hhid⟩
  wp_auto
  simp only [decide_eq_false Hl]
  wp_auto
  iunfold recHidden at Hhid
  icases Hhid with ⟨#Hinv, ⟨%us, #HU, #HUs⟩, %Huf⟩
  rcases c with ⟨typ, crc, data, u⟩
  simp only at Huf ⊢
  -- `Type`
  cases typ
  all_goals (iunfold recCell at HTc; simp only)
  all_goals first
    | (icases HTc with %Hpt; subst Hpt; wp_auto)
    | (ihave %Hpt := typedPointsto_not_null pt _ _ $$ HTc
       simp only [decide_eq_false Hpt, Bool.not_false]
       wp_auto
       wp_apply (wp_AppendTag _ _ _ _ (by word) (by word)) $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
       wp_apply wp_AppendVarint $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩)
  -- `Crc`
  all_goals cases crc
  all_goals (iunfold recCell at HCc; simp only)
  all_goals first
    | (icases HCc with %Hpc; subst Hpc; wp_auto)
    | (ihave %Hpc := typedPointsto_not_null pc _ _ $$ HCc
       simp only [decide_eq_false Hpc, Bool.not_false]
       wp_auto
       wp_apply (wp_AppendTag _ _ _ _ (by word) (by word)) $$ [$Hb $Hcap] as %b3 ⟨Hb, Hcap⟩
       wp_apply wp_AppendVarint $$ [$Hb $Hcap] as %b4 ⟨Hb, Hcap⟩)
  -- `Data`
  all_goals cases data
  all_goals (iunfold recBytes at HDc; simp only)
  all_goals first
    | (icases HDc with %Hds; subst Hds; wp_auto)
    | (icases HDc with ⟨%Hds, #Hd⟩
       simp only [decide_eq_false Hds, Bool.not_false]
       wp_auto
       wp_apply (wp_AppendTag _ _ _ _ (by word) (by word)) $$ [$Hb $Hcap] as %b5 ⟨Hb, Hcap⟩
       wp_apply wp_AppendBytes $$ [$Hb $Hcap $Hd] as %b6 ⟨Hb, Hcap, -⟩)
  -- the unknown fields, then the result
  all_goals
    wp_apply wp_slice_append $$ [$Hb $Hcap $HUs] as %b7 ⟨Hb, Hcap, -⟩
    iapply HΦ
    simp only [recEnc, optVarintField, optBytesField, Option.map, Wire.tag, Wire.FVal.payload,
      models_lab.pbcodec.zext32, List.append_assoc, List.nil_append]
    iframe

end proof

end EtcdGrove
end Perennial
