/- Lean-first (no Rocq counterpart).

# `etcd/dist/client`: the auth workload's shares (#50 F7 S12, `notes/etcd-dist-f7.md`, "Handoff W-6")

The shares the auth class's start would hand its machines, at the global ghost state (`[Gg : GooseGlobalGS]`), the
candidates for `wlShare`'s and `wlNodeShare`'s kind-5 arms (`client/Shares.lean`, the lead's, still `False` there):
- `authShare eps ns`: the orchestrator's, `RunAuth.spec`'s precondition but its machine-local parts (an auth-on view
  `Γ` with distinct auth names, the raft names `γR` tied to `Γ`'s requested log, a start state `σ₀` with no change;
  every member's `leaseMember`, the KV invariant `kvInvOn`, the empty log's lower bound, the client halves `etcdKV`
  and `authHistView`, and `principalsShare` at the members' client addresses `eps` and the principal machines `ns`);
- `authNodePre addr eps`: principal machine `addr`'s, `nodeAuthPre` without its level token and pure machine facts
  (`nodeAuthPre_of`), at the members' client addresses **not rotated** (`NodeMain`'s auth arm hands its `eps` to
  `principalOp` unrotated, where `NodeMain.spec` gives the share at `rotateL eps c`: W-6's rotation item).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.PrincipalWire
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.LeaseDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcd_dist.authd
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext] [GoLocalContext] [go.Semantics]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

/-- **The auth workload's orchestrator share** (see the file header). -/
def authShare (eps ns : List GoString) : IProp GF :=
  iprop(∃ (Γ : DistView) (γR : ServerRaftNames) (σ₀ : KVState),
    ⌜Γ.auth = true ∧ γR.raft.log = Γ.kv.rlog ∧ (∀ a b : w64, Γ.au a = Γ.au b → a = b) ∧
      (∀ cs ∈ σ₀.changes, cs = [])⌝ ∗
    ([∗list] a ∈ eps, leaseMember (Gg := Gg) Γ a) ∗ kvInvOn γR Γ.kv srvAuthSt0 ∗ srvReqLogLb γR [] ∗
    etcdKV Γ.kv σ₀ ∗ authHistView Γ.kv [srvAuthSt0] ∗ principalsShare (Gg := Gg) Γ γR eps ns)

/-- **A principal machine's share** (see the file header). -/
def authNodePre (addr : GoString) (eps : List GoString) : IProp GF :=
  iprop(∃ (Γ : DistView) (γR : ServerRaftNames),
    ⌜Γ.auth = true ∧ ∀ a b : w64, Γ.au a = Γ.au b → a = b⌝ ∗
    membersAt (Gg := Gg) eps Γ ∗ svcAddr (Gg := Gg) (principalSvcG (Gg := Gg) Γ γR eps) addr)

end shares

section onMachine
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [go_etcd_io.raft.v3.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

/-- **`nodeAuthPre` from the principal machine's share** and the machine's level token, at the boot's pure facts
(as `nodeWatchPre_of`). -/
theorem nodeAuthPre_of (addr : GoString) (eps : List GoString) (hV : Nonempty (WEnv GF))
    (htb : threadBound GF ≤ 2 ^ 30) (hpl : plainEndpoints eps)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    levelTok 0 ∗ authNodePre (Gg := hG.goose_globalGS) addr eps ⊢ nodeAuthPre addr eps := by
  iintro ⟨Hlt, Hw⟩
  iunfold authNodePre at Hw
  icases Hw with ⟨%Γ, %γR, %Hp, #Hm, #Ha⟩
  iunfold nodeAuthPre
  iframe Hlt
  iexists Γ, γR
  isplitr
  · ipureintro; exact ⟨Hp.1, Hp.2, hV, htb, hpl, hAs⟩
  isplitl []
  · iexact Hm
  · iexact Ha

end onMachine

end etcd_dist_client
end EtcdGrove
end Perennial

end
