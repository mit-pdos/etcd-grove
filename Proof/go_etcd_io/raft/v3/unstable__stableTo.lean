/-
Port of `election_proof/proof_unstable__stableTo.v` (857d09190).
-/
module

public import Spec.go_etcd_io.raft.v3.unstable__stableTo
public import Spec.go_etcd_io.raft.v3.unstable__maybeTerm
public import Spec.go_etcd_io.raft.v3.unstable__shrinkEntriesArray

@[expose] public section

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
/-- Close a no-hit exit: nothing changed (after `log_exit`, which rewrote the logger to
`ok ulg`). -/
local macro "no_hit" : tactic => `(tactic| (
  rw [← Hulg]
  iapply HΦ
  isplitl
  · close_unstable
  ipureintro
  refine ⟨fun Hh => ?_, fun _ => rfl⟩))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
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
  intro u us id Hsoff Hnw
  wp_start as H
  iNamed H
  open_unstable
  wp_auto
  wp_apply wp_unstable_maybeTerm u us id.index' Hsoff Hnw $$ [Hu Hents Hents_cap]
    as %gt %ok ⟨Hun, %Hok1, %Hok2⟩
  · close_unstable
  open_unstable_again
  icases Hents with #Hents
  ihave %Hlen := ownSlice_len $$ Hents
  ihave #Hulgv : isLoggerVal uv.logger' $$ [Hlogger]
  · iexact Hlogger
  iunfold isLoggerVal at Hulgv
  icases Hulgv with ⟨%ulg, %Hulg, #Hlg⟩
  cases ok
  · -- not in the log: no hit
    wp_auto
    log_exit Hulg
    no_hit
    exact absurd (Hok1.2 (Or.inl Hh.1)) Bool.false_ne_true
  wp_auto
  by_cases Hlt : uint.Z id.index' < uint.Z us.offset
  · -- the snapshot's index: no hit
    rw [decide_eq_true (by word)]
    wp_auto
    log_exit Hulg
    no_hit
    exact absurd Hh.1.1 (by omega)
  rw [decide_eq_false (by word)]
  wp_auto
  obtain ⟨⟨Hr, e, He, rfl⟩⟩ | ⟨sid, Hs, Hi, -⟩ := Hok2 rfl
  rotate_left
  · exfalso; have := Hsoff sid Hs; rw [Hi] at Hlt; omega
  by_cases Ht : e.Term' = id.term'
  rotate_left
  · -- a different term at `id.index`: no hit
    rw [decide_eq_false Ht]
    wp_auto
    log_exit Hulg
    no_hit
    obtain ⟨-, e', He', Ht'⟩ := Hh
    rw [He] at He'; cases He'; exact absurd Ht' Ht
  rw [decide_eq_true Ht]
  wp_auto
  -- the hit: drop the persisted prefix
  have Hnum : sint.Z (id.index' + W64 1 - us.offset) =
      uint.Z id.index' + 1 - uint.Z us.offset := by word
  ihave %Hwf := ownSlice_wf $$ Hents
  rw [ite_eq_left ⟨by word, by word, Hwf.2⟩]
  icases (ownSlice_slice (id.index' + W64 1 - us.offset) uv.entries'.len uv.entries'
      DFrac.discard us.ents ⟨by word, by word, by word⟩).1 $$ Hents with ⟨-, #Hents2, -⟩
  ihave Hents_cap := (ownSliceCap_slice uv.entries' (id.index' + W64 1 - us.offset) _
      ⟨by word, by word, Hwf.2⟩).1 $$ Hents_cap
  wp_auto
  wp_apply wp_max2_uint64
  have Hsub : subslice (sint.nat (id.index' + W64 1 - us.offset)) (sint.nat uv.entries'.len)
      us.ents = us.ents.drop (uint.Z id.index' + 1 - uint.Z us.offset).toNat := by
    rw [subslice_def, List.take_of_length_le (by word)]
    congr 1
    word
  rw [Hsub]
  wp_apply wp_unstable_shrinkEntriesArray u
      { us with ents := us.ents.drop (uint.Z id.index' + 1 - uint.Z us.offset).toNat,
                offset := id.index' + W64 1,
                inprogress := w64Max us.inprogress (id.index' + W64 1) } $$ [Hu Hents_cap] as Hun
  · iapply ownUnstable_intro $$ Hu Hents_cap Hents2 Hsnap Hlogger
    ipureintro; exact ⟨rfl, rfl⟩
  iapply HΦ
  isplitl [Hun]
  · iexact Hun
  ipureintro
  refine ⟨fun _ => rfl, fun Hn => absurd ?_ Hn⟩
  exact ⟨⟨by omega, by omega⟩, e, He, Ht⟩

end proof

end EtcdGrove
end Perennial
