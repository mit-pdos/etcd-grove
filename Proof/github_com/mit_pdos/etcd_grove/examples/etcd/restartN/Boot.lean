/- Lean-first (no Rocq counterpart).

# restartN's restart contracts from `bootstrap.specRestart` (premises to axioms, 2026-11-27)

`Run(k)`'s named premises (`premises`, `Defs.lean`) were the closed theorem's Iris premise `Hprem₅`: each
member's first-start contract (`etcdstart.bootPremise`) and each stop candidate's restart contract
(`etcdstart.bootPremiseR`). The restart contracts now come from the interim axiom `bootstrap.wp_proofRestart`
(`bootstrap.specRestart`), at Go's values:
* `BootGoN`: the pure facts that the member ids, peers, contexts and directory `Run(k)` names are what Go
  computes from each member's configuration (`bootGo.*` at the cluster token and the member's name), the
  members' names and URLs plain (putget's `BootGo1` for `k` members);
* `bootPremises`: the first-start contracts alone, what the closed theorem still takes as an Iris premise
  (the first start of `k` members in one process: `bootstrap` sends `GET /members` to the members already
  serving, which no spec of `bootstrap` covers yet; the packet's option (b));
* `premises_of_specRestart`: `premises` from `bootPremises` and the restart contracts the axiom gives.

A defs module: it takes the axiom's statement as a hypothesis and imports no proof.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BootRestart
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BootBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart

section pure
variable [GooseExts]

/-- **`bootstrap`'s values for `Run(k)`'s members are Go's** (pure; putget's `BootGo1` for the `k` members):
each id is not one of raft's local targets, and for member `i` (`(members k)[i]`, id `ids[i]`), at every
URLs `urlsN` admits for it (all of which agree on the initial cluster: every member's name to its one peer
URL), Go's peers are `ps`, its contexts `ctxs`, its directory `dirN (members k) ids`, the member's id
`ids[i]`, and the URLs and names plain, not empty and fitting (`bootURLsPlain`, `bootNamesPlain`, `urlsNe`,
`initMapOk`). Checked by `TestMemberIDs` (`restartN_test.go`) for the ids at every `k ≤ 300`. -/
structure BootGoN (k : Nat) (ids ps : List w64) (ctxs : List (List w8)) : Prop where
  idRaft : ∀ id ∈ ids, id ≠ W64 18446744073709551615 ∧ id ≠ W64 18446744073709551614
  go : ∀ (i : Nat) (m : GMember) (id : w64), (members k)[i]? = some m → ids[i]? = some id →
    ∀ U : BootURLs, urlsN (members k) m U →
      bootGo.bootURLsPlain U ∧ bootGo.ps U token = ps ∧ bootGo.ctxs U token = ctxs ∧
        bootGo.dir U token = dirN (members k) ids ∧ (bootGo.memberOf U token m.Name').id = id ∧
        bootNamesPlain U ∧ bootGo.urlsNe U ∧ bootGo.initMapOk U token

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

/-- **The first-start contracts of `Run(k)`'s members** (persistent; `premises`' first part): the one Iris
premise of the closed theorem left for this cluster (see the file header). -/
def bootPremises (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) : IProp GF :=
  iprop([∗list] m; id ∈ members k; ids,
    etcdstart.bootPremise N ps (LogEntry.toEntries boot 0) ctxs (dirN (members k) ids) token
      m.Name' (etcdstart.urlsN (members k) m) id)

instance bootPremises_persistent (k N : Nat) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) :
    Persistent (bootPremises (GF := GF) k N ids ps ctxs boot) := by
  unfold bootPremises; infer_instance

/-- **The stop candidates' restart contracts from `bootstrap.specRestart`** (`premises`' second part), at
Go's values (`BootGoN`) and the cluster's boot facts (`BootFacts`: the boot log the node API's log of the
peers and contexts, the peers a permutation of the ids). -/
theorem restartPremises_of_specRestart [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (hb : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.specRestart (GF := GF) (hG := hG))
    (k N : Nat) (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (hfips : crypto.fips140.GodebugFips140Off) (Hbf : BootFacts ids ps ctxs boot)
    (Hbg : BootGoN k ids ps ctxs) (hlen : (members k).length = ids.length) (j : Nat) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      [∗list] m; id ∈ (members k).drop j; ids.drop j,
        etcdstart.bootPremiseR N ps (LogEntry.toEntries boot 0) ctxs (dirN (members k) ids) token
          m.Name' (etcdstart.urlsN (members k) m) id := by
  iintro #Hpkg
  iapply BigSepL2.bigSepL2_intro
  isplit
  · ipureintro; simp [hlen]
  iintro !> %i %m %id %Hm %Hid
  rw [List.getElem?_drop] at Hm Hid
  have hidm : id ∈ ids := List.mem_of_getElem? Hid
  iapply (bootPremiseR_of_specRestart hb N ps (LogEntry.toEntries boot 0) ctxs (dirN (members k) ids)
    token m.Name' (etcdstart.urlsN (members k) m) id hfips (Hbg.idRaft id hidm)
    (fun U hu => by
      obtain ⟨hplain, hps, hctxs, hdir, hidU, hnp, hune, hiok⟩ := Hbg.go (j + i) m id Hm Hid U hu
      exact ⟨hplain, hps, hctxs, hdir, hidU, ⟨boot, Hbf.boot, rfl⟩,
        memBoot_bootLog U token boot hplain hnp (by rw [hps, hctxs]; exact Hbf.boot), hune, hiok⟩)
    (Hbf.perm.mem_iff.2 hidm))
  iexact Hpkg

/-- **`Run(k)`'s named premises from the first-start contracts and `bootstrap.specRestart`**. -/
theorem premises_of_specRestart [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (hb : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.specRestart (GF := GF) (hG := hG))
    (k N : Nat) (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (hfips : crypto.fips140.GodebugFips140Off) (Hbf : BootFacts ids ps ctxs boot)
    (Hbg : BootGoN k ids ps ctxs) (hlen : (members k).length = ids.length) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      bootPremises (GF := GF) k N ids ps ctxs boot -∗ premises (GF := GF) k N ids ps ctxs boot := by
  iintro #Hpkg #Hbp
  iunfold premises
  iunfold bootPremises at Hbp
  isplitl []
  · iexact Hbp
  · iapply (restartPremises_of_specRestart hb k N ids ps ctxs boot hfips Hbf Hbg hlen (k - nStop k))
    iexact Hpkg

end defs

end etcd_restartN
end EtcdGrove
end Perennial

end
