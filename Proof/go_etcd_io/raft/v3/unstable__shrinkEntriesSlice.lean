/-
Lean-first (etcd-io/raft#96).
-/
module

public import Spec.go_etcd_io.raft.v3.unstable__shrinkEntriesSlice
public import Spec.go_etcd_io.raft.v3.unstable__doEntriesNeedCompaction
public import Spec.go_etcd_io.raft.v3.unstable__compactEntriesSlice

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem unstable.shrinkEntriesSlice.wp_proof
    (wp_unstable_doEntriesNeedCompaction : unstable.doEntriesNeedCompaction.spec (GF := GF) (hG := hG))
    (wp_unstable_compactEntriesSlice : unstable.compactEntriesSlice.spec (GF := GF) (hG := hG)) :
    unstable.shrinkEntriesSlice.spec (GF := GF) (hG := hG) := by
  intro u us k Hk0 Hkl
  wp_start as H
  iNamed H
  open_unstable
  icases Hents with #Hents
  ihave %Hlen := entsPts_len $$ Hents
  wp_auto
  by_cases Hk : k = uv.entries'.len
  · -- every entry is persisted: `nil`
    rw [decide_eq_true Hk]
    wp_auto
    have Hd : us.ents.drop (sint.Z k).toNat = [] := List.drop_of_length_le (by word)
    iapply HΦ
    rw [Hd]
    iapply ownUnstable_intro $$ Hu
    · iapply ownSliceCap_nil
    · iapply entsPts_nil
    · iexact Hsnap
    · iexact Hpksn
    · iexact Hlogger
    · ipureintro; exact ⟨rfl, rfl⟩
  rw [decide_eq_false Hk]
  wp_auto
  wp_apply wp_unstable_doEntriesNeedCompaction u us k $$ [Hu Hents_cap] as %b Hun
  · close_unstable
  cases b
  · -- re-slice
    open_unstable_again
    icases Hents with #Hents
    ihave %Hlen2 := entsPts_len $$ Hents
    ihave Hents' := Hents
    iunfold entsRO at Hents'
    iunfold entsPts at Hents'
    icases Hents' with ⟨%ls, #Hls, #Hb⟩
    ihave %Hlsl := ownSlice_len $$ Hls
    ihave %Hwf := ownSlice_wf $$ Hls
    wp_auto
    rw [ite_eq_left ⟨Hk0, by word, Hwf.2⟩]
    icases (ownSlice_slice k uv.entries'.len uv.entries' DFrac.discard ls
        ⟨Hk0, by word, by word⟩).1 $$ Hls with ⟨-, #Hls2, -⟩
    ihave Hents_cap := (ownSliceCap_slice uv.entries' k _ ⟨Hk0, by word, Hwf.2⟩).1 $$ Hents_cap
    have Hsub : subslice (sint.nat k) (sint.nat uv.entries'.len) us.ents =
        us.ents.drop (sint.Z k).toNat := by
      rw [subslice_def, List.take_of_length_le (by word)]
    wp_auto
    iapply HΦ
    iapply ownUnstable_intro $$ Hu Hents_cap
    · rw [← Hsub]
      iunfold entsRO; iunfold entsPts; iexists _; iframe Hls2
      iapply entsBig_subslice $$ Hb
    · iexact Hsnap
    · iexact Hpksn
    · iexact Hlogger
    · ipureintro; exact ⟨rfl, rfl⟩
  · -- copy into a fresh array
    wp_auto
    wp_apply wp_unstable_compactEntriesSlice u us k Hk0 Hkl $$ [Hun] as Hun
    · iexact Hun
    iapply HΦ
    iexact Hun

end proof

end EtcdGrove
end Perennial
