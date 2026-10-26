/-
Port of `election_proof/proof_unstable__shrinkEntriesArray.v` (857d09190).
-/
module

public import Spec.go_etcd_io.raft.v3.unstable__shrinkEntriesArray

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem unstable.shrinkEntriesArray.wp_proof :
    unstable.shrinkEntriesArray.spec (GF := GF) (hG := hG) := by
  intro u us
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
  wp_auto
  by_cases He : us.ents = []
  · -- empty: `nil`
    wp_if_destruct
    · iapply HΦ
      iapply ownUnstable_intro $$ Hu
      · iapply ownSliceCap_nil
      · rw [He]; iapply entsPts_nil
      · iexact Hsnap
      · iexact Hpksn
      · iexact Hlogger
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
    · exfalso; simp [He] at Hlen; word
  · wp_if_destruct
    · exfalso; apply He; apply List.eq_nil_of_length_eq_zero; word
    wp_if_destruct
    · -- copy into an array of exactly the right size
      wp_apply wp_slice_make2 (V := Loc) as %sl ⟨Hsl, Hsl_cap⟩
      · ipureintro; word
      wp_apply +noauto wp_slice_copy $$ [$Hsl $Hls] as %n ⟨%Hn, Hsl, -⟩
      have Hcp : (ls.take (List.replicate (sint.nat uv.entries'.len)
            (zero_val Loc)).length ++
          (List.replicate (sint.nat uv.entries'.len) (zero_val Loc)).drop ls.length) =
          ls := by
        rw [List.length_replicate, List.take_of_length_le (by rw [Hlsl.1]; exact Nat.le_refl _),
          List.drop_of_length_le (by rw [List.length_replicate, Hlsl.1]; exact Nat.le_refl _), List.append_nil]
      rw [Hcp]
      ipersist Hsl
      wp_auto
      iapply HΦ
      iapply ownUnstable_intro $$ Hu Hsl_cap
      · iunfold entsRO; iunfold entsPts; iexists ls; iframe Hsl Hb
      · iexact Hsnap
      · iexact Hpksn
      · iexact Hlogger
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
    · iapply HΦ
      close_unstable

end proof

end EtcdGrove
end Perennial
