/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: the client machine's boot, over the interim cross-machine axioms (`notes/putget-dist-plan.md` §12)

`client_boot`: the client machine's boot program (`putget.initialize' #()`, then `putget.Client(client)`,
its result discarded) is safe from the client's share of the distributed start (`clientShare` at the
cluster's view) and its whole start (`DistBootWpST`); the registration rights of its packages' metric
IDs are allocated here, the machine's own registry ghost state (prom-registry, as `member_boot`). Linked: `Client.wp_proof` at its callees' linked results (`zap.NewNop`'s, `etcdstart`'s `Link`,
`context`'s, and `etcd_dist.Client_Put_dist.wp_proof`/`Client_Get_dist.wp_proof` over the interim
trust-boundary axioms `etcd_dist.KV_Put_dist.wp_proof`/`KV_Get_dist.wp_proof`), `putget`'s `wp_initialize'`. The client touches no file: its
files' and listeners' start resources are unused. `Client` checks its address (`AddrOk`), and
that a valid address is a plain endpoint is proved (`etcd_dist.addrOk_plainEndpoint`); `errors.As`'s target `rpctypes.EtcdError` from the package's
method sets (`rpctypesEtcdError_asTarget`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Client
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.AdequacyMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientPutDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientGetDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.InitLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_uber_org.zap.NewNop
public import Perennial.Proof.context.Link
public import Proof.context.Link
public import Proof.context.WithTimeoutBackground
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init
public import Net.Statement.DistBridgeExts

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.raft.v3 Net

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

set_option maxHeartbeats 1600000 in
/-- **The client machine's boot** (see the file header). -/
theorem client_boot [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [_root_.Perennial.errors.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [log.NewModel]
    (client : GoString) (hlc : client.length + 1 < 2 ^ 63) (σc : state)
    [G : GooseGlobalGS .hasLC putgetGF] [π : NetProtoGS] (Γ : etcd_dist.DistView) (mid : w64) :
    DistBootWpST putgetThreads putgetSteps (bootClient client) σc (clientShareIf (GF := putgetGF) client Γ mid) := by
  intro hG hGG hL hrb hT
  unfold putgetSteps at hrb
  unfold putgetThreads at hT
  obtain ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  simp only at hGG hL
  subst hGG hL
  letI hG : HeapGS .hasLC putgetGF := ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩
  haveI := etcdFsSemOk
  haveI : ThreadBoundLe putgetGF (2 ^ 30) := ⟨Nat.le_trans (Nat.le_of_eq hT) (by decide)⟩
  iintro Hshare - Hgs Htok
  -- (decision 1b) the main thread's level-0 token, for `Client`
  icases (threadTok_level0 (GF := putgetGF)).1 $$ Htok with ⟨Hl0, -⟩
  iunfold clientShareIf at Hshare
  -- (prom-registry) the machine's registration rights: a fresh ghost map of its packages' IDs, the
  -- machine's registry name (as `member_boot`)
  imod (prometheus.regKeys_alloc (GF := putgetGF)
    github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.regQs putget_regQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS putgetGF := ⟨γreg⟩
  ihave Hns := prometheus.idToks_regsFree (GF := putgetGF)
    github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.regQs $$ Hregs
  ihave Hown := ownInitializing_of_empty
    (github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.getIsPkgInit (GF := putgetGF)) $$ Hgs
  imodintro
  -- `putget.initialize' #()`
  unfold bootClient
  wp_apply (github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.getIsPkgInit_wf) $$ [Hown Hns]
    as ⟨-, #Hpkg⟩
  · iframe
  (try wp_auto)
  -- `putget.Client(client)`, its result discarded
  wp_apply (Client.wp_proof zap.NewNop.wp_proof etcdstart.wp_NewClient context.wp_Background
      context.WithTimeoutBackground.wp_proof context.wp_ErrAny
      (etcd_dist.Client_Put_dist.wp_proof etcd_dist.KV_Put_dist.wp_proof)
      (etcd_dist.Client_Get_dist.wp_proof etcd_dist.KV_Get_dist.wp_proof)
      (AddrOk.wp_proof decimal.wp_proof) mvcc.api.mvccApi_names_nonempty_law_holds
      client Γ mid hlc
      EtcdGrove.rpctypesEtcdError_asTarget) $$ [Hl0 Hshare] as %b -
  · iframe
  (try wp_auto)
  all_goals first | done | (ipureintro; rfl) | itrivial

end etcd_putget_dist
end EtcdGrove
end Perennial

end
