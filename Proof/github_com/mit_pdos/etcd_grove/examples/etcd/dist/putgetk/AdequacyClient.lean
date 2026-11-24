/- Lean-first (no Rocq counterpart).

# `etcd/dist/putgetk`: the client machine's boot (`notes/putget-dist-plan.md` §13b, plan item 4)

`client_bootK`: the client's boot program (`putgetk.initialize' #()`, then `putgetk.Client(ep)`, its result
discarded) is safe from its share of the start (`⌜ep ≠ ""⌝ -∗ ⌜plainEndpoint ep⌝ ∗ clientShare ep γE mid
putgetPub`) and its whole start, as putget's `client_boot` (`dist/putget/AdequacyClient.lean`): `Client.wp_proof`
at `AddrOK`'s proof and putget's `Client.wp_proof` at its linked callees and the interim axioms
`Client_Put_dist`, `Client_Get_dist`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Client
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.AddrOK
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.decimal
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.AdequacyMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.AdequacyClient

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.raft.v3 Net etcd_putget_dist

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

set_option maxHeartbeats 1600000 in
/-- **The client machine's boot** (see the file header). -/
theorem client_bootK [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF,
      ContextReadErrs (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF,
      ContextErrsClient (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (ep : GoString) (σc : state)
    [G : GooseGlobalGS .hasLC putgetGF] [π : NetProtoGS] (γE : GName) (mid : w64) :
    DistBootWpSL srvLevelK (2 ^ 28 - 1) (bootClient ep) σc
      (iprop(⌜ep ≠ []⌝ -∗ ⌜plainEndpoint ep⌝ ∗ clientShare ep γE mid (putgetPub (GF := putgetGF)))) := by
  intro hG hGG hL hlo hrb hT
  obtain ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  simp only at hGG hL
  subst hGG hL
  letI hG : HeapGS .hasLC putgetGF := ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩
  haveI : ContextReadErrs (GF := putgetGF) (hG := hG) := Hctx hG
  haveI : ContextErrsClient (GF := putgetGF) (hG := hG) := Hcec hG
  haveI := etcdFsSemOk
  haveI : ThreadBoundLe putgetGF (2 ^ 31) := ⟨by rw [hT]; omega⟩
  iintro Hshare - Hgs -
  imod (prometheus.regKeys_alloc (GF := putgetGF)
    github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.regQs putgetk_regQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS putgetGF := ⟨γreg⟩
  ihave Hns := prometheus.idToks_regsFree (GF := putgetGF)
    github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.regQs $$ Hregs
  ihave Hown := ownInitializing_of_empty
    (github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.getIsPkgInit (GF := putgetGF)) $$ Hgs
  imodintro
  -- `putgetk.initialize' #()`
  unfold bootClient
  wp_apply (github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.getIsPkgInit_wf) $$ [Hown Hns]
    as ⟨-, #Hpkg⟩
  · iframe
  (try wp_auto)
  -- `putgetk.Client(ep)`, its result discarded
  wp_apply (Client.wp_proof (AddrOK.wp_proof decimal.wp_proof)
      (etcd_putget_dist.Client.wp_proof zap.NewNop.wp_proof etcdstart.wp_NewClient context.wp_Background
        context.WithTimeoutBackground.wp_proof context.wp_ErrAny
        etcd_dist.Client_Put_dist.wp_proof etcd_dist.Client_Get_dist.wp_proof
        mvcc.api.mvccApi_names_nonempty_law_holds)
      ep γE mid EtcdGrove.rpctypesEtcdError_asTarget) $$ [Hshare] as %b -
  · iframe; iframe #
  (try wp_auto)
  all_goals first | done | (ipureintro; rfl) | itrivial

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
