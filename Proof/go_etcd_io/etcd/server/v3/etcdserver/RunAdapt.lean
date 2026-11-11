/-
# The gRPC runs' bundle and adapters, for etcd's server (per-type stage B3)

Scope r5 §3.3-§3.4: a run of one of etcd's KV, lease or auth handlers, or of the watch loops, holds
one loan per level of its thread token: `raftPool`'s `lgMu` reader at level 1, the inner pool `I`
(`leadTimeMu` ∗ `E.RD`) at level 2, the run pool (a store reader token, a reader slot of the read
loop's lock and one of `bemu`) at level 3.

* `srvRunBundle s E γr`: the run's level 0 (which the lease handlers' level-0 pools take) and the
  three pools' resources, which the handlers are proved against
  (`grpcMethodOkMd` at this resource).
* `srvRunOk_of_pools`, `srvStreamRunOk_of_pools`: a handler proved at the bundle meets grpc's run
  contract, from the built part (`srvRevokeBuilt`: levels 1 and 2) and the run pool (`srvRunPool`,
  level 3), given `srvLevels` (levels 0-3 of a token exist).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServe
public import Proof.google_golang_org.grpc.InvGrpcRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A gRPC run's bundle** (see the file header): its own level 0 (the lease handlers' lessor and
lease pools) and the loans of its levels 1, 2 and 3. -/
def srvRunBundle (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(levelTok 0 ∗ srvLgReader s ∗ (srvLeadTimeReader s ∗ E.RD) ∗
    (mvcc.api.mvccReaders E.γ 1 ∗ srvReadReader s γr ∗ srvBemuReader s))

end defs

section adapt
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A unary handler proved at the bundle meets grpc's run contract** (r5 §3.4): from the built
part's pools (levels 1 and 2) and the run pool (level 3), with `srvLevels`. -/
theorem srvRunOk_of_pools {Req Rep : ProtoMsg GF} (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (mh : val) (srv : GoInterface) (ics : List GoFunc) (Spec : GrpcSpecMd Req Rep)
    (HL : srvLevels (GF := GF)) :
    □ grpcMethodOkMd mh srv ics (srvRunBundle s E γr) Spec ∗ srvRevokeBuilt s E ∗
      srvRunPool s E γr ⊢
    grpcRunOkMd mh srv ics Spec := by
  iintro ⟨#Hm, #Hb, #Hr⟩
  ihave ⟨%γ₁, %γ₂, #H1, #H2⟩ := srvRevokeBuilt_runPools s E $$ Hb
  iunfold srvRunPool at Hr
  icases Hr with ⟨%γ₃, #H3⟩
  iapply (grpcRunOkMd_of_pools mh srv ics Spec _ _ _ raftPoolN srvRevokeInnerN srvRunN γ₁ γ₂ γ₃
    (by have := HL; unfold srvLevels srvLevelK srvRevokeK at this; omega))
  iframe #

/-- **A stream handler proved at the bundle meets grpc's stream run contract** (r5 §3.4), as
`srvRunOk_of_pools`. -/
theorem srvStreamRunOk_of_pools {Req Rep : StreamMsg GF} (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (mh : val) (srv : GoInterface) (sics : List GoFunc)
    (Up : Nat → Req.M → IProp GF) (Spec : GrpcMd → StreamSpec Rep) (HL : srvLevels (GF := GF)) :
    □ grpcStreamMethodOk mh srv sics (srvRunBundle s E γr) Up Spec ∗ srvRevokeBuilt s E ∗
      srvRunPool s E γr ⊢
    grpcStreamRunOk mh srv sics Up Spec := by
  iintro ⟨#Hm, #Hb, #Hr⟩
  ihave ⟨%γ₁, %γ₂, #H1, #H2⟩ := srvRevokeBuilt_runPools s E $$ Hb
  iunfold srvRunPool at Hr
  icases Hr with ⟨%γ₃, #H3⟩
  iapply (grpcStreamRunOk_of_pools mh srv sics Up Spec _ _ _ raftPoolN srvRevokeInnerN srvRunN
    γ₁ γ₂ γ₃ (by have := HL; unfold srvLevels srvLevelK srvRevokeK at this; omega))
  iframe #

end adapt

end EtcdGrove
end Perennial
