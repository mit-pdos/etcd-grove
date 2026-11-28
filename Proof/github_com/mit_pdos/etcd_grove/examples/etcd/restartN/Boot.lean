/- Lean-first (no Rocq counterpart).

# restartN's contracts from `bootstrap`'s interim axioms (premises to axioms, 2026-11-27)

`Run(k)`'s named premises (`premises`, `Defs.lean`) were the closed theorem's Iris premise `Hprem₅`: each
member's first-start contract (since 2026-11-27 `etcdstart.bootPremiseF` at the members' peer addresses,
`peersFree`) and each stop candidate's restart contract (`etcdstart.bootPremiseR`). They now come from the
interim axioms, at Go's values: the first starts from `bootstrap.wp_proofUnserved` (`bootstrap.specUnserved`:
`startMembers` builds every member before it serves any, and lends each first boot every member's peer address),
the restarts from `bootstrap.wp_proofRestart` (`bootstrap.specRestart`):
* `BootGoN`: the pure facts that the member ids, peers, contexts and directory `Run(k)` names are what Go
  computes from each member's configuration (`bootGo.*` at the cluster token and the member's name), the
  members' names and URLs plain (putget's `BootGo1` for `k` members);
* `firstPremises_of_specUnserved`, `restartPremises_of_specRestart`: the two parts;
* `premises_of_specs`: `premises` from the two axioms.

A defs module: it takes the axioms' statements as hypotheses and imports no proof.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BootRestart
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BootBridge
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BootUnserved
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Dir

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

/-- **The members' first-start contracts from `bootstrap.specUnserved`** (`premises`' first part), at Go's
values (`BootGoN`), the cluster's boot facts (`BootFacts`) and the shape `StartMembers`' URLs have
(`urlsN_shapeUnserved`, at the members' peer addresses: the frame `peersFree`). -/
theorem firstPremises_of_specUnserved [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (hb : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.specUnserved (GF := GF) (hG := hG))
    (k N : Nat) (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (hfips : crypto.fips140.GodebugFips140Off) (Hbf : BootFacts ids ps ctxs boot)
    (Hbg : BootGoN k ids ps ctxs) (hlen : (members k).length = ids.length) (hk : k ≤ 1000) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      [∗list] m; id ∈ members k; ids,
        etcdstart.bootPremiseF (peersFree (members k)) N ps (LogEntry.toEntries boot 0) ctxs
          (dirN (members k) ids) token m.Name' (etcdstart.urlsN (members k) m) id := by
  iintro #Hpkg
  iapply BigSepL2.bigSepL2_intro
  isplit
  · ipureintro; simp [hlen]
  iintro !> %i %m %id %Hm %Hid
  have hidm : id ∈ ids := List.mem_of_getElem? Hid
  have hmm : m ∈ members k := List.mem_of_getElem? Hm
  iapply (bootPremiseF_of_specUnserved hb N ps (LogEntry.toEntries boot 0) ctxs (dirN (members k) ids)
    token m.Name' (etcdstart.urlsN (members k) m) id ((members k).map (fun m : GMember => m.Peer'))
    (by have h := restartNAddrs_lit k hk; unfold restartNAddrs at h; exact h)
    hfips (Hbg.idRaft id hidm)
    (fun U hu => urlsN_shapeUnserved (members k) (members_names_nodup k hk) m hmm U hu)
    (fun U hu => by
      obtain ⟨hplain, hps, hctxs, hdir, hidU, hnp, hune, hiok⟩ := Hbg.go i m id Hm Hid U hu
      exact ⟨hplain, hps, hctxs, hdir, hidU, ⟨boot, Hbf.boot, rfl⟩, hnp, hune, hiok⟩))
  iexact Hpkg

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

/-- **`Run(k)`'s named premises from `bootstrap.specUnserved` and `bootstrap.specRestart`**. -/
theorem premises_of_specs [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (hbU : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.specUnserved (GF := GF) (hG := hG))
    (hbR : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.specRestart (GF := GF) (hG := hG))
    (k N : Nat) (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (hfips : crypto.fips140.GodebugFips140Off) (Hbf : BootFacts ids ps ctxs boot)
    (Hbg : BootGoN k ids ps ctxs) (hlen : (members k).length = ids.length) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      premises (GF := GF) k N ids ps ctxs boot := by
  iintro #Hpkg
  iunfold premises
  isplitl []
  · iintro !> %hk
    iapply (firstPremises_of_specUnserved hbU k N ids ps ctxs boot hfips Hbf Hbg hlen hk)
    iexact Hpkg
  · iapply (restartPremises_of_specRestart hbR k N ids ps ctxs boot hfips Hbf Hbg hlen (k - nStop k))
    iexact Hpkg

end defs

end etcd_restartN
end EtcdGrove
end Perennial

end
