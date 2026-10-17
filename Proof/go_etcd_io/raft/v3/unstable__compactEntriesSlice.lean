/-
Lean-first (etcd-io/raft#96).
-/
module

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

theorem unstable.compactEntriesSlice.wp_proof :
    unstable.compactEntriesSlice.spec (GF := GF) (hG := hG) := by
  intro u us k Hk0 Hkl
  wp_start as H
  iNamed H
  open_unstable
  icases Hents with #Hents
  ihave %Hlen := entsPts_len $$ Hents
  ihave Hents' := Hents
  iunfold entsRO at Hents'
  iunfold entsPts at Hents'
  icases Hents' with ⟨%ls, #Hls, #Hb⟩
  ihave %Hlsl := ownSlice_len $$ Hls
  ihave %Hwf := ownSlice_wf $$ Hls
  wp_auto
  wp_apply wp_slice_make2 (V := Loc) as %sl ⟨Hsl, Hsl_cap⟩
  · ipureintro; word
  rw [ite_eq_left ⟨Hk0, by word, Hwf.2⟩]
  icases (ownSlice_slice k uv.entries'.len uv.entries' DFrac.discard ls
      ⟨Hk0, by word, by word⟩).1 $$ Hls with ⟨-, #Hls2, -⟩
  wp_apply +noauto wp_slice_copy $$ [$Hsl $Hls2] as %n ⟨%Hn, Hsl, -⟩
  have Hsubl : (subslice (sint.nat k) (sint.nat uv.entries'.len) ls).length =
      sint.nat (uv.entries'.len - k) := by
    rw [subslice_length]; word
  have Hcp : (subslice (sint.nat k) (sint.nat uv.entries'.len) ls).take
        (List.replicate (sint.nat (uv.entries'.len - k)) (zero_val Loc)).length ++
      (List.replicate (sint.nat (uv.entries'.len - k)) (zero_val Loc)).drop
        (subslice (sint.nat k) (sint.nat uv.entries'.len) ls).length =
      subslice (sint.nat k) (sint.nat uv.entries'.len) ls := by
    rw [List.length_replicate, Hsubl, List.take_of_length_le (by rw [Hsubl]; exact Nat.le_refl _),
      List.drop_of_length_le (by rw [List.length_replicate]; exact Nat.le_refl _), List.append_nil]
  rw [Hcp]
  ipersist Hsl
  have Hsub : subslice (sint.nat k) (sint.nat uv.entries'.len) us.ents =
      us.ents.drop (sint.Z k).toNat := by
    rw [subslice_def, List.take_of_length_le (by word)]
  wp_auto
  iapply HΦ
  iapply ownUnstable_intro $$ Hu Hsl_cap
  · rw [← Hsub]
    iunfold entsRO; iunfold entsPts; iexists _; iframe Hsl
    iapply entsBig_subslice $$ Hb
  · iexact Hsnap
  · iexact Hpksn
  · iexact Hlogger
  · ipureintro; exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
