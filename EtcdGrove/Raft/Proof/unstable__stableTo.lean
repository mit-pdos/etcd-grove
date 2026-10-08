/-
Port of `election_proof/proof_unstable__stableTo.v` (857d09190).
-/
import EtcdGrove.Raft.Spec.unstable__stableTo
import EtcdGrove.Raft.Spec.unstable__maybeTerm
import EtcdGrove.Raft.Spec.unstable__shrinkEntriesArray

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

set_option hygiene false in
/-- One of the three `Infof`-and-return exits (Rocq `log_exit`). -/
local macro "log_exit" Hulg:ident : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨-, -⟩
  wp_auto
  rw [$Hulg:ident]
  wp_auto
  wp_apply Logger.wp_logf _ _ _ _ (by simp [logMethods]) $$ Hlg))

set_option hygiene false in
/-- Close a no-hit exit: nothing changed. -/
local macro "no_hit" Hulg:ident : tactic => `(tactic| (
  iapply HΦ
  unfold ownUnstable
  iframe Hu
  iframe # ∗
  ipureintro
  refine ⟨rfl, $Hulg:ident, fun Hh => ?_, fun _ => ⟨rfl, rfl⟩⟩))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `max` on `uint64` (Rocq: the framework's `wp_max2_uint64`; the same private lemma as
in `Proof/Progress__BecomeProbe.lean`). -/
private theorem wp_max2_uint64 (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.uint64, go.uint64])) (Val #x)) (Val #y))
    {{ RET #(w64Max x y); True }} := by
  wp_start
  wp_if_destruct
  · rw [show w64Max x y = x by unfold w64Max; simp_all]
    iapply HΦ; itrivial
  · rw [show w64Max x y = y by unfold w64Max; rw [ite_eq_right_iff.2 (fun h => absurd h (by omega))]]
    iapply HΦ; itrivial

theorem unstable.stableTo.wp_proof
    (wp_unstable_maybeTerm : unstable.maybeTerm.spec (GF := GF) (hG := hG))
    (wp_unstable_shrinkEntriesArray : unstable.shrinkEntriesArray.spec (GF := GF) (hG := hG)) :
    unstable.stableTo.spec (GF := GF) (hG := hG) := by
  intro u uv uents snap id ulg Hsoff Hnw Hulg
  wp_start as H
  iNamed H
  iunfold ownUnstable at Hun
  iNamed Hun
  icases Hents with #Hents
  ihave %Hlen := ownSlice_len $$ Hents
  wp_alloc u_ptr as u; wp_pures; wp_alloc id_ptr as id; wp_pures; wp_load; wp_pures; wp_load
  wp_pures
  wp_apply wp_unstable_maybeTerm _ _ _ snap id.index' Hsoff Hnw $$ [Hu Hents_cap]
    as %gt %ok ⟨Hun, %Hok1, %Hok2⟩
  · unfold ownUnstable; simp only [named]; iframe # ∗
  wp_pures; wp_alloc ok_ptr as ok; wp_pures; wp_alloc gt_ptr as gt; wp_pures; wp_store; wp_pures
  wp_store; wp_pures; wp_load; wp_pures; iclear ok
  iunfold ownUnstable at Hun
  icases Hun with ⟨Hu, Hents_cap, -⟩
  simp only [named]
  cases ok
  · -- not in the log: no hit
    wp_pures; wp_load; wp_pures
    -- TODO(no-wp-auto): macro `log_exit` runs wp_auto: wp_pures | wp_pures; wp_load; wp_pures; wp_load; wp_pures | wp_pures | wp_pures; iclear u id gt
    log_exit Hulg
    no_hit Hulg
    exact absurd (Hok1.2 (Or.inl Hh.1)) Bool.false_ne_true
  wp_pures; wp_load; wp_load; wp_pures; wp_load; wp_pures
  by_cases Hlt : uint.Z id.index' < uint.Z uv.offset'
  · -- the snapshot's index: no hit
    rw [decide_eq_true (by word)]
    wp_pures; wp_load; wp_pures
    -- TODO(no-wp-auto): macro `log_exit` runs wp_auto: wp_pures | wp_pures; wp_load; wp_pures; wp_load; wp_pures | wp_pures | wp_pures; iclear u id gt
    log_exit Hulg
    no_hit Hulg
    exact absurd Hh.1.1 (by omega)
  rw [decide_eq_false (by word)]
  wp_pures; wp_load; wp_pures; wp_load; wp_pures
  obtain ⟨⟨Hr, e, He, rfl⟩⟩ | ⟨sid, Hs, Hi, -⟩ := Hok2 rfl
  rotate_left
  · exfalso; have := Hsoff sid Hs; rw [Hi] at Hlt; omega
  by_cases Ht : e.Term' = id.term'
  rotate_left
  · -- a different term at `id.index`: no hit
    rw [decide_eq_false Ht]
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear gt
    -- TODO(no-wp-auto): macro `log_exit` runs wp_auto: wp_pures | wp_pures; wp_load; wp_pures; wp_load; wp_pures | wp_pures | wp_pures; iclear u id
    log_exit Hulg
    no_hit Hulg
    obtain ⟨-, e', He', Ht'⟩ := Hh
    rw [He] at He'; cases He'; exact absurd Ht' Ht
  rw [decide_eq_true Ht]
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_alloc num_ptr as num
  wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load
  wp_pures; wp_load; wp_pures; iclear gt num
  -- the hit: drop the persisted prefix
  have Hnum : sint.Z (id.index' + W64 1 - uv.offset') =
      uint.Z id.index' + 1 - uint.Z uv.offset' := by word
  ihave %Hwf := ownSlice_wf $$ Hents
  rw [ite_eq_left ⟨by word, by word, Hwf.2⟩]
  icases (ownSlice_slice (id.index' + W64 1 - uv.offset') uv.entries'.len uv.entries'
      DFrac.discard uents ⟨by word, by word, by word⟩).1 $$ Hents with ⟨-, #Hents2, -⟩
  ihave Hents_cap := (ownSliceCap_slice uv.entries' (id.index' + W64 1 - uv.offset') _
      ⟨by word, by word, Hwf.2⟩).1 $$ Hents_cap
  wp_pures; wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_store
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear id
  wp_apply wp_max2_uint64
  wp_pures; wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_pures; iclear u
  have Hsub : subslice (sint.nat (id.index' + W64 1 - uv.offset')) (sint.nat uv.entries'.len)
      uents = uents.drop (uint.Z id.index' + 1 - uint.Z uv.offset').toNat := by
    rw [subslice_def, List.take_of_length_le (by word)]
    congr 1
    word
  rw [Hsub]
  wp_apply wp_unstable_shrinkEntriesArray _ _
      (uents.drop (uint.Z id.index' + 1 - uint.Z uv.offset').toNat) $$ [Hu Hents_cap] as %sl Hun
  · unfold ownUnstable
    simp only [named]
    iframe Hu Hents_cap
    iframe # ∗
  wp_pures
  iapply HΦ
  iframe Hun
  ipureintro
  refine ⟨rfl, rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun Hn => absurd ?_ Hn⟩
  exact ⟨⟨by omega, by omega⟩, e, He, Ht⟩

end proof

end EtcdGrove
end Perennial
