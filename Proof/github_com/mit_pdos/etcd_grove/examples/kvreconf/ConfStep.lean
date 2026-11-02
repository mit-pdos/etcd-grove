/-
Lean-first (no Rocq counterpart).

# A replica's configuration, one committed entry at a time (2026-10-29, track C)

Each replica carries `confAt γ k m` for its applied index `k` and its configuration `m` (`r.index`,
`r.cs`; `Rule.lean`'s header). Past a committed entry it moves:

- a normal entry: `confAt_noConf` (`kvr_confAt_normal`);
- a conf entry: the store's decision (`confPolicy_decide` under `kvrConfN`: the recorded one, the
  rule's `kvrRule` at `m`), then `confAt_decided` gives the configuration after it
  (`kvr_confAt_conf`). The decision is `apply o` exactly when the rule accepts (`validConf`'s answer,
  `ConfOk`), else `skip` -- the `confDecided γ k .skip` that `skippedIn` collects for the
  `ApplyConfChange`/`Advance` calls after a rejection.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Rule

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The store's namespace for its conf-change decisions (`confPolicy`'s invariant). -/
def kvrConfN : Namespace := nroot.@"kvreconf_conf"

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

/-- Past a normal committed entry, the configuration stays. -/
theorem kvr_confAt_normal (γ : Cluster) (l : List LogEntry) (k : Nat) (e : LogEntry)
    (m : Membership) (hk : l[k]? = some e) (he : ¬ e.isConfChange) :
    isCommittedLogLb (GF := GF) γ l ∗ confAt γ k m ⊢ confAt γ (k + 1) m := by
  have hlt : k < l.length := (List.getElem?_eq_some_iff.mp hk).1
  apply confAt_noConf γ l k (k + 1) m _ (by omega) (by omega)
  intro j e' hj1 hj2 hj
  have : j = k := by omega
  subst this
  rw [hk] at hj; cases hj; exact he

/-- **Past a committed conf entry** (see the file header): the store's decision, recorded, and the
configuration after it. -/
theorem kvr_confAt_conf (γ : Cluster) (N : Namespace) (E : CoPset) (l : List LogEntry) (k : Nat)
    (e : LogEntry) (m : Membership) (hk : l[k]? = some e) (he : e.isConfChange)
    (hE : ↑kvrConfN ⊆ E) :
    ⊢ isCluster (GF := GF) γ N ∗ confPolicy γ kvrConfN kvrRule ∗ isCommittedLogLb γ l ∗
        confAt γ k m ={E}=∗
      ∃ m', ⌜(ConfDecision.ofRule (kvrRule (l.take k) m e)).step m = some m'⌝ ∗
        confDecided γ k (ConfDecision.ofRule (kvrRule (l.take k) m e)) ∗ confAt γ (k + 1) m' := by
  obtain ⟨m', hm'⟩ := kvrRule_step (l.take k) m e
  iintro ⟨#Hc, #Hp, #Hl, #Hm⟩
  imod confPolicy_decide γ N kvrConfN E kvrRule l k e m m' hk he hE hm' $$ [$Hc $Hp $Hl $Hm] with #Hd
  imodintro
  ihave H := confAt_decided γ k m _ $$ [$Hm $Hd]
  icases H with ⟨%m'', %h'', #H''⟩
  iexists m''
  iframe Hd H''
  ipureintro; exact h''

end laws

end kvreconf
end EtcdGrove
end Perennial
