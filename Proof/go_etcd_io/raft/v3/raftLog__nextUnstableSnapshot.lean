/- `raftLog.nextUnstableSnapshot`, Lean-first (D22 S-d3a, 2026-10-21). -/
module

public import Spec.go_etcd_io.raft.v3.raftLog__nextUnstableSnapshot
public import Spec.go_etcd_io.raft.v3.unstable__nextSnapshot

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

theorem raftLog.nextUnstableSnapshot.wp_proof
    (wp_unstable_nextSnapshot : unstable.nextSnapshot.spec (GF := GF) (hG := hG)) :
    raftLog.nextUnstableSnapshot.spec (GF := GF) (hG := hG) := by
  intro l ls
  wp_start as H
  iNamed H
  iNamed Hlog
  wp_auto
  lend_unstable
  wp_apply wp_unstable_nextSnapshot _ (unstableOf lv ls) $$ [$Hun] as %p ⟨Hun, %Hp, Hsv⟩
  reopen_unstable
  iapply HΦ
  isplitl [Hl Huents_cap Huents HStorage]
  · reseal_raftLog
  simp only [unstableOf] at Hp
  isplitr
  · ipureintro; exact Hp
  icases Hsv with (%Hn | ⟨%sid, %sv, %Hs, Hsv⟩)
  · ileft; ipureintro; exact Hn
  iright
  iexists sid, sv
  iframe Hsv
  ipureintro
  obtain ⟨H1, H2, H3, H4, H5⟩ := Hs
  have Hst : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := H1 ▸ Hstore
  exact ⟨H1, H2, H3, H4, Hst.2.2.1, H5⟩

end proof

end EtcdGrove
end Perennial
