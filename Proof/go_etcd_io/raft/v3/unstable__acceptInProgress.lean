/-
Port of `election_proof/proof_unstable__acceptInProgress.v` (857d09190).
-/
module

public import Spec.go_etcd_io.raft.v3.unstable__acceptInProgress

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

theorem unstable.acceptInProgress.wp_proof :
    unstable.acceptInProgress.spec (GF := GF) (hG := hG) := by
  intro u us Hidx Hnw
  wp_start as H
  iNamed H
  open_unstable
  icases Hents with #Hents
  ihave %Hlen := ownSlice_len $$ Hents
  wp_auto
  by_cases He : us.ents = []
  · -- no entries: only the snapshot flag
    wp_if_destruct
    · exfalso; simp [He] at Hlen; word
    wp_if_destruct <;>
    · iapply HΦ
      isplitl
      · close_unstable
      ipureintro
      simp [He]
  · obtain ⟨es, e, Hes⟩ := List.eq_nil_or_concat us.ents |>.resolve_left He
    have Hl : us.ents.length = es.length + 1 := by simp [Hes]
    have Hle : us.ents[us.ents.length - 1]? = some e := by
      rw [Hes]; simp
    have Heidx := Hidx _ _ Hle
    wp_if_destruct
    rotate_left
    · exfalso; word
    have Hbnd : 0 ≤ sint.Z (uv.entries'.len - W64 1) ∧
        sint.Z (uv.entries'.len - W64 1) < sint.Z uv.entries'.len := by
      constructor <;> word
    rw [ite_eq_left Hbnd]
    have Hk : (sint.Z (uv.entries'.len - W64 1)).toNat = us.ents.length - 1 := by word
    have Hle' : us.ents[(sint.Z (uv.entries'.len - W64 1)).toNat]? = some e := by rw [Hk]; exact Hle
    icases ownSlice_elem_acc (sint.Z (uv.entries'.len - W64 1)) e uv.entries' _ us.ents Hbnd.1 Hle'
      $$ Hents with ⟨#He, -⟩
    iStructNamedSuffix He "_e"
    wp_auto
    wp_if_destruct <;>
    · iapply HΦ
      isplitl
      · close_unstable
      ipureintro
      refine ⟨fun h => absurd h He, fun _ => ?_⟩
      word

end proof

end EtcdGrove
end Perennial
