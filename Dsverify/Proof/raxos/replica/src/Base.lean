/-
The package fact of QuePaxa's replica, `srcState` (the lab's `PkgState.lean`): its
`Consensus_ServiceDesc` variable holds, for good, the generated descriptor of service `Consensus`
(its three methods with their generated handlers, no streams), for the recorder's
`grpc.RegisterService` (`descOk`). Proved by the generated `Init.lean` (`etc/dsv/quepaxa.py`).
-/
module

public import Dsverify.GeneratedProof.raxos.replica.src
public import Net.Proof.net.Base
public import Dsverify.Proof.github_com.go_redis.redis.v8.Base
public import Dsverify.Proof.google_golang_org.grpc.Base
public import Dsverify.Proof.google_golang_org.grpc.codes.Base
public import Dsverify.Proof.google_golang_org.grpc.status.Base
public import Dsverify.Proof.raxos.common.Base
public import Dsverify.Proof.raxos.configuration.Base
public import Dsverify.Proof.raxos.proto.Base
public import Dsverify.Proof.raxos.proto.client.Base
public import Perennial.Proof.context.Base
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.log.Base
public import Perennial.Proof.reflect.Base
public import Perennial.Proof.sort.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.strings.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.time.Base
public import Proof.bufio.PkgInit
public import Dsverify.Proof.google_golang_org.protobuf.Base
public import Proof.math.rand.Base
public import Proof.os.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace raxos.replica.src

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `raxos/replica/src`'s package-level state: `Consensus_ServiceDesc` (persistent): the
descriptor of service `Consensus`, its three methods with their generated handlers, no streams. -/
def srcState : IProp GF :=
  iprop(∃ sd : google_golang_org.grpc.ServiceDesc,
    globalAddr raxos.replica.src.Consensus_ServiceDesc ↦□ sd ∗
    ⌜sd.ServiceName' = go!"Consensus" ∧ sd.Streams'.len = W64 0⌝ ∗
    sd.Methods' ↦*□ ([⟨go!"ESP", functions raxos.replica.src._Consensus_ESP_Handler []⟩,
      ⟨go!"FetchBatches", functions raxos.replica.src._Consensus_FetchBatches_Handler []⟩,
      ⟨go!"InformDecision", functions raxos.replica.src._Consensus_InformDecision_Handler []⟩] :
      List google_golang_org.grpc.MethodDesc))

instance srcState_persistent : Persistent (srcState (GF := GF)) := by
  unfold srcState; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.raxos.replica.src :=
  define_is_pkg_init srcState
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.raxos.replica.src :=
  build_get_is_pkg_init_wf

end def_

end raxos.replica.src
end Perennial
