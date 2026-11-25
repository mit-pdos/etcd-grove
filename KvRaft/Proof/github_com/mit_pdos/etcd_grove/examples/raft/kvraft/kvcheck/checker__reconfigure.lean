/- Lean-first (no Rocq counterpart).

Proof of `KvRaft/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/kvcheck/checker__reconfigure.lean`: a
loop over `sleep`; each round a request of kind `ReqDisrupt` whose payload `EncodeDisrupt` builds (its fact
`reqOk_disrupt`: the payload is two words), its answer dropped.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__reconfigure
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__request
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__randomID
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.sleep
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__conf
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__randomChange
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.PutConfChange

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

theorem checker.reconfigure.wp_proof (wp_sleep : sleep.spec (GF := GF) (hG := hG))
    (wp_randomID : checker.randomID.spec (GF := GF) (hG := hG))
    (wp_conf : checker.conf.spec (GF := GF) (hG := hG))
    (wp_randomChange : checker.randomChange.spec (GF := GF) (hG := hG))
    (wp_PutConfChange : PutConfChange.spec (GF := GF) (hG := hG))
    (wp_request : checker.request.spec (GF := GF) (hG := hG)) :
    checker.reconfigure.spec (GF := GF) (hG := hG) := by
  intro F c γ ls stop γc HconfOk
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
    wp_apply wp_conf F c γ ls $$ [$Hpkg $Hc] as %csp ⟨%cs, #Hcs⟩
    wp_apply wp_randomChange c γ ls csp cs Hls.1 $$ [$Hpkg $Hck $Hcs] as %cc %o ⟨Hcc, %Ho⟩
    try wp_auto
    wp_apply wp_randomID c γ ls Hls.1 $$ [$Hpkg $Hck] as %id %Hid
    try wp_auto
    ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
    ihave Hncap := ownSliceCap_nil (V := w8) (GF := GF)
    wp_apply wp_PutConfChange slice.nil [] cc (DFrac.own 1) o $$ [$Hkv $Hnil $Hncap $Hcc]
      as %pl ⟨Hpl, -, -⟩
    have Hlen : ((([] : List w8) ++ encCC o).length : Int) + 17 < 2 ^ 63 := by
      have := encCC_length o; simp only [List.nil_append]; omega
    wp_apply wp_request F c γ ls id (W8 3) pl ([] ++ encCC o) (DFrac.own 1) Hid.1 Hid.2 Hlen
      $$ [$Hpkg $Hc $Hpl] as %r %ok -
    · rw [reqOk_conf]
      ipureintro; exact HconfOk _
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
