/-
**M2, the apply side: the Probe's proofs** (`notes/m2-apply-plan.md`, "The Probe"; 2026-10-31).
Imported by nothing (as the Drafts): the first proofs over the approved drafted statements, to test
that they are provable before the switch.

* **The commit step (G4, item 6)**: a compaction proposal's update over the KV invariant in the
  cluster's mode (`kv_prop_au_cmp`, `reqPropOkD`'s compaction form). Its leading step
  (`cmpReach_reqLb`), at the caller's mask, reads the proposer's KV certificate through the
  certificates' invariant (`kvCertInv`) and turns it into a lower bound of the server's log of
  requested entries (`srvReqLogLb_of_rlogLb`); inside the update the lower bound is a prefix of the
  committed log (`srvReqLogLb_prefix`), where the invariant records the compaction's claim
  (`cmpLogOk`): its revision one of the model's before the entry.
* **The transfer (S3-3, item 8)**: an entry of the committed log gets its compaction claim from the
  KV invariant's (`kv_entry_claim`, at `kv_log_plain`'s hypotheses, which `applyEntryNormal`'s proof
  holds; its pure core `cmpEntryOk_transfer`).
* **G1**: the workload clause over the switch's invariant (`clusterWorkloadOk_ofD`, with
  `batchWaitOk_of_workD`): `clusterWorkloadOk_of`'s proof over `kvInvD` and the drafted shapes.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.M2ApplyDraft
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **The transfer (S3-3, item 8), pure**: a committed log `A ++ [m]` whose requested entries are
a prefix of the server's log `L`'s (no fillers in `L`) gets the entry's claim from `L`'s claims:
`m`, if a compaction, is one of `L`'s entries, at the position after the prefix `A'` of `L` with
`A`'s requested entries, and the model of `A'` is `A`'s (`kvModel_eqv`). -/
theorem cmpEntryOk_transfer (γ : ServerRaftNames) (γk : KVNames) (cmp : Bool)
    (A L : List EntryModel) (m : EntryModel)
    (hAm : srvIdxOkW γ.ai0 (A ++ [m])) (hL : srvIdxOkW γ.ai0 L)
    (hnf : ∀ e ∈ L, ¬ e.toLE.isFiller ∧ ¬ e.toLE.isEmptyV2)
    (h : opsOf ((A ++ [m]).map EntryModel.toLE) <+: L.map EntryModel.toLE)
    (hc : uint.Z γk.c0 ≤ uint.Z γ.ai0) (hcl : cmpLogOk γk cmp L) :
    cmpEntryOk γk cmp A m := by
  intro ht hd rq hdec hk
  have hA : srvIdxOkW γ.ai0 A := srvIdxOkW_prefix _ A _ hAm (List.prefix_append _ _)
  have hf : ¬ m.toLE.isFiller := fun hf => hd hf.1
  have hv : ¬ m.toLE.isEmptyV2 := fun hv => by
    have h2 : m.typ = W32 2 := hv.2
    rw [ht] at h2; exact absurd h2 (by decide)
  have hops : opsOf ((A ++ [m]).map EntryModel.toLE) =
      opsOf (A.map EntryModel.toLE) ++ [m.toLE] := by
    rw [List.map_append, opsOf_append]
    simp [opsOf, hf, hv]
  rw [hops] at h
  -- the prefix of `L` with `A`'s requested entries, and the entry after it
  obtain ⟨A', hA'L, hAA'⟩ := srv_eqv_prefix γ A L hA hL hnf
    ((List.prefix_append _ _).trans h)
  have hA'nf : ∀ x ∈ A'.map EntryModel.toLE, ¬ x.isFiller ∧ ¬ x.isEmptyV2 := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hnf y (hA'L.subset hy)
  have hlen : (opsOf (A.map EntryModel.toLE)).length = A'.length := by
    rw [hAA'.2.2, opsOf_nofill _ hA'nf, List.length_map]
  have hA'eq : A' = L.take A'.length := List.prefix_iff_eq_take.1 hA'L
  obtain ⟨t, htl⟩ := h
  have hget : (L.map EntryModel.toLE)[A'.length]? = some m.toLE := by
    rw [← htl, List.append_assoc, List.getElem?_append_right (by omega), ← hlen, Nat.sub_self]
    rfl
  rw [List.getElem?_map, Option.map_eq_some_iff] at hget
  obtain ⟨m', hm', he⟩ := hget
  have h1 := congrArg LogEntry.type he
  have h2 := congrArg LogEntry.data he
  simp only [EntryModel.toLE] at h1 h2
  have := hcl A'.length m' hm' (h1 ▸ ht) (h2 ▸ hd) rq (h2 ▸ hdec) hk
  rw [← hA'eq, ← (kvModel_eqv γ γk A A' hAA' hc).1] at this
  exact this

end pure

section probe
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/- (Stage 4c: `cmpReach_reqLb` and `kv_prop_au_cmp` moved to `KVLemmas.lean`.) -/

/-- **The transfer (S3-3, item 8)**: an entry `m` of the committed log after `A` (a lower bound of
it, as `applyEntryNormal`'s proof holds) gets its claim from the KV invariant's, at the invariant's
mode. At `⊤`, as `kv_log_plain`. -/
theorem kv_entry_claim (γ : ServerRaftNames) (γk : KVNames)
    (A : List EntryModel) (m : EntryModel) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ (A ++ [m]) ={⊤}=∗
      ⌜cmpEntryOk γk γk.cmp A m⌝ := by
  iintro #Hinv #Hr #HB
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L (A ++ [m]) $$ Hr HL HB with ⟨HL, %Hp⟩
  ihave %HBi := srvRLogLb_idx γ (A ++ [m]) $$ HB
  imod Hclose $$ [HL Hσ] with -
  · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
  imodintro
  ipureintro
  obtain ⟨-, -, hc0, -, -, hcl⟩ := Hok
  exact cmpEntryOk_transfer γ γk γk.cmp A L m HBi Hp.1 Hp.2.1 Hp.2.2 hc0 hcl

end probe

end EtcdGrove
end Perennial
