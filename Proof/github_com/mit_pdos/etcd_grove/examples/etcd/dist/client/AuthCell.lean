/-
**authlease's cell at the cluster view** (F7 stage S5, `notes/etcd-dist-f7.md`, "Handoff S5-3", "Next"):
the single-process cell (`authlease/Cell.lean`) is over the KV names `γk` only, so the dist workload
`RunAuthLease` allocates it at `Γ.kv` and reuses its updates, all but `cell_grantAu`, whose offer is the
single-process `clientGrant` of one member's `E`/`ρ`. At the view a grant's offer is `writeAuD Γ.kv P
(.leaseGrant id ttl) L₀`, told `opGrantD`'s `writeGrantG` with the principal's binding `userOk P`; the
grant's freshness (`writeGrantG_grant_fresh`) is generic in that binding, so the port is `cell_grantAuD`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseCell
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthViewDist

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Iris.Std go_etcd_io.etcd.server.v3.etcdserver client
open etcd_dist etcd_dist.authd etcd_authlease

section cell
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A grant's update under the cell, at the view** (`cell_grantAu` with the offer `writeAuD`'s: any
principal `P`, at a TTL at most the maximum; the revocable mode): it records its id in `gs` and tells the
caller so. -/
theorem cell_grantAuD (γk : KVNames) (γc : CellNames) (P : Option GoString) (ttl : w64)
    (L₀ : List EntryModel) (httl : sint.Z ttl ≤ maxLeaseTTL) (hrev : γk.lm = .revocable) :
    cellInv (GF := GF) γk γc ⊢ □ ∀ id : w64, kvAu1G γk (kvOpStep (.leaseGrant id ttl))
      (opGrantD γk P (.leaseGrant id ttl) L₀) (gsHas γc id) := by
  iintro #Hinv
  imodintro
  iintro %id
  ihave #Hau := cell_writeAu γk γc (.leaseGrant id ttl) (opGrantD γk P (.leaseGrant id ttl) L₀)
    (gsHas γc id) $$ [Hinv]
  · isplitl []
    · iexact Hinv
    iintro !> %σ %ids %ps %gs %d %HS Hids Ha HG
    ihave HG : writeGrantG γk srvAuthSt0 (fun hm => iprop(⌜userOk P hm.username⌝))
        (irrLeaseGrant id ttl) L₀ σ $$ [HG]
    · iunfold opGrantD at HG; iexact HG
    ihave %Hf := writeGrantG_grant_fresh γk srvAuthSt0 (fun hm => iprop(⌜userOk P hm.username⌝))
      id ttl L₀ σ hrev $$ HG
    iunfold cellAuth at Ha
    icases Ha with ⟨Hp, Hg, Hd, Hdo⟩
    imod (monoListAuthOwn_update_app (GF := GF) (γ := γc.gs) (l := gs) [id]) $$ Hg with ⟨Hg, #Hgl⟩
    imodintro
    iexists ps, gs ++ [id], d
    iframe Hids
    isplitr
    · ipureintro; exact cellOk_grant HS id ttl httl (cellOk_fresh HS id Hf)
    isplitl [Hp Hg Hd Hdo]
    · iunfold cellAuth; iframe Hp Hg Hd Hdo
    iunfold gsHas
    iexists gs ++ [id]
    iframe Hgl
    ipureintro; simp
  iexact Hau

/-- `writeAuD`'s grant offers from the cell (`cell_grantAuD` at the workload's TTL). -/
theorem cell_grantWriteAuD (γk : KVNames) (γc : CellNames) (P : Option GoString) (ttl : w64)
    (L₀ : List EntryModel) (httl : sint.Z ttl ≤ maxLeaseTTL) (hrev : γk.lm = .revocable) :
    cellInv (GF := GF) γk γc ⊢ □ ∀ id : w64, writeAuD γk P (.leaseGrant id ttl) L₀ (gsHas γc id) := by
  iintro #Hinv
  ihave #Hau := cell_grantAuD γk γc P ttl L₀ httl hrev $$ Hinv
  imodintro
  iintro %id
  iunfold writeAuD
  imodintro
  ispecialize Hau $$ %id
  iexact Hau

end cell

end etcd_dist_client
end EtcdGrove
end Perennial
