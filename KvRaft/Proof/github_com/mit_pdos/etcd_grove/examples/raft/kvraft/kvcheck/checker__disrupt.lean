/- Lean-first (no Rocq counterpart).

Proof of `KvRaft/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/kvcheck/checker__disrupt.lean`: a
loop over `sleep`; each round a request of kind `ReqDisrupt` whose payload `EncodeDisrupt` builds (its fact
`reqOk_disrupt`: the payload is two words), its answer dropped.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__disrupt
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__request
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__randomID
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.below
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.sleep
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.EncodeDisrupt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode Net kvraft go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions]

theorem checker.disrupt.wp_proof (wp_sleep : sleep.spec (GF := GF) (hG := hG))
    (wp_randomID : checker.randomID.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_EncodeDisrupt : EncodeDisrupt.spec (GF := GF) (hG := hG))
    (wp_request : checker.request.spec (GF := GF) (hG := hG)) :
    checker.disrupt.spec (GF := GF) (hG := hG) := by
  intro F c γ ls stop γc
  wp_start as ⟨#Hc, #Hstop⟩
  ihave #Hc0 := Hc
  iunfold isCheckerP at Hc0
  icases Hc0 with ⟨#Hck, %Hls, -, -⟩
  ihave #Hkv : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft $$ []
  · iPkgInit
  try wp_auto
  wp_for
  wp_apply wp_sleep _ stop γc $$ [$Hpkg $Hstop] as %b -
  try wp_auto
  wp_if_destruct
  · -- another round
    wp_apply wp_randomID c γ ls Hls.1 $$ [$Hpkg $Hck] as %id %Hid
    wp_apply wp_below _ $$ [$Hpkg] as %what -
    wp_apply wp_randomID c γ ls Hls.1 $$ [$Hpkg $Hck] as %to -
    wp_apply wp_EncodeDisrupt what to $$ [$Hkv] as %s ⟨Hs, -⟩
    wp_apply wp_request F c γ ls id (W8 4) s (u64Le what ++ u64Le to) (DFrac.own 1) Hid.1 Hid.2
        (by simp [u64Le_length]) $$ [$Hpkg $Hc $Hs] as %r %ok -
    · rw [reqOk_disrupt]
      ipureintro; exact ⟨what, to, rfl⟩
    try wp_auto
    wp_for_post
    iframe
  · -- stop
    wp_if_destruct
    · try wp_auto
      iapply HΦ
      itrivial
    · exfalso
      cases b <;> simp_all

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
