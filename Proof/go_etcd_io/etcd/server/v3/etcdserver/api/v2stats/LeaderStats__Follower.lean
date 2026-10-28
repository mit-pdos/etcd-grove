/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/LeaderStats__Follower.lean`
(`leader.go`; until D43 M5a, 2026-10-26, the trust boundary): under the stats' mutex, a lookup in
the followers' map (the caller's, `v2stats.lsFollowers`), a fresh `*FollowerStats` stored if absent.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.LeaderStats__Follower

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Assumptions]

theorem v2stats.LeaderStats.Follower.wp_proof :
    v2stats.LeaderStats.Follower.spec (GF := GF) (hG := hG) := by
  intro ls name
  wp_start as ⟨#Hmu, Hfo⟩
  iunfold v2stats.isLeaderStats at Hmu
  iunfold v2stats.lsFollowers at Hfo
  icases Hfo with ⟨%fm, %FM, #Hf, Hm, %Hnn⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, -⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 $$ [$Hm] as Hm
  (try wp_auto)
  cases hk : FM !! name with
  | some fs0 =>
    simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
    (try wp_auto)
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
    · inext; itrivial
    (try wp_auto)
    iapply HΦ
    isplitr
    · ipureintro; exact Hnn _ _ hk
    iunfold v2stats.lsFollowers
    iexists fm, FM
    iframe #; iframe
    ipureintro; exact Hnn
  | none =>
    simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
    (try wp_auto)
    ihave %Hr0 := typedPointsto_not_null $$ «$r0»
    wp_apply wp_mapInsert $$ [Hm] as Hm
    · iframe Hm
    (try wp_auto)
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
    · inext; itrivial
    (try wp_auto)
    iapply HΦ
    isplitr
    · ipureintro; exact Hr0
    iunfold v2stats.lsFollowers
    iexists fm, _
    iframe #; iframe
    ipureintro
    intro k v h
    by_cases hkn : k = name
    · subst hkn; simp at h; subst h; exact Hr0
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkn)] at h; exact Hnn _ _ h

end proof

end EtcdGrove
end Perennial
