/-
Lean-first (no Rocq counterpart). Trace-check's Q8 stage 1, slice 29n (2026-11-11; `notes/decisions.md`,
"Q8 stage 1 (slice 29n)"): **the frozen Draft's `traceConfChangeEvent.tracedSpec`, proved from the
code** (`TracedHooksDraft.lean`), both modes. Untraced, the nil check; traced, the `TracingConfChange`
built from the new configuration's incoming voters (`cfg.Voters[0].Slice()`, formatted), the properties'
map `{"cc": cc}` made read-only, and `traceEvent` with raft's state (at the old configuration) lent
whole.

(2026-11-12, trace-check step 4) The proof moved to `traceConfChangeEvent.wp_proof`, whose spec is now
one for both modes over a read-only lending of raft's state (`RaftReadLend`); the Draft's statement is
its instance (`tracedSpec_of_spec`).
Raft-internal (not on `etc/api/raft.txt`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedHooksDraft
public import Proof.go_etcd_io.raft.v3.TracedMsg
public import Spec.go_etcd_io.raft.v3.traceEvent
public import Spec.go_etcd_io.raft.v3.formatConf
public import Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__Slice
public import Proof.go_etcd_io.raft.v3.traceConfChangeEvent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The Draft's statement, an instance of `traceConfChangeEvent.spec`**: raft's state lent whole
(`raftReadLend_self`), the mode the node's. -/
theorem traceConfChangeEvent.tracedSpec_of_spec (h : traceConfChangeEvent.spec (GF := GF) (hG := hG)) :
    traceConfChangeEvent.tracedSpec (GF := GF) (hG := hG) := by
  intro c cn r id s cfgv prsm prs pvs tl Q
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hnew, Hfire⟩ HΦ
  cases htr : s.gh.tr with
  | none =>
    iapply h cfgv r tl none (CCEvOf id s c cn) Q iprop(emp) $$ [$Hpkg $Htl $Hfire]
    · iapply trOwn_none_intro
    inext
    iintro ⟨-, HQ⟩
    iapply HΦ
    iframe
  | some γd =>
    iapply h cfgv r tl (some γd) (CCEvOf id s c cn) Q
        iprop(ownRaftPhysCV c c.voters r id s ∗ ownConfigC cn cfgv prsm prs pvs)
      $$ [$Hpkg $Htl $Hfire Hphys Hnew]
    · iapply (trOwn_some γd _).2
      iexists c, cn, id, s, prsm, prs, pvs, ownRaftPhysCV c c.voters r id s
      iframe Hphys Hnew
      isplitr
      · iapply raftReadLend_self
      isplitr
      · ipureintro; exact fun _ h => h
      iintro H; iexact H
    inext
    iintro ⟨HR, HQ⟩
    icases (trOwn_some γd _).1 $$ HR with ⟨Hphys, Hnew⟩
    iapply HΦ
    iframe

/-- **`traceConfChangeEvent.tracedSpec`** (the Draft's, frozen), from the code. -/
theorem traceConfChangeEvent.tracedSpec_proof
    (wp_traceEvent : traceEvent.spec (GF := GF) (hG := hG))
    (wp_Slice : quorum.MajorityConfig.Slice.spec (GF := GF) (hG := hG))
    (wp_formatConf : formatConf.spec (GF := GF) (hG := hG)) :
    traceConfChangeEvent.tracedSpec (GF := GF) (hG := hG) :=
  traceConfChangeEvent.tracedSpec_of_spec (traceConfChangeEvent.wp_proof wp_traceEvent wp_Slice wp_formatConf)

end proof

end EtcdGrove
end Perennial
