/-
transport/netrpc, the server side closed: `Bindings.lean`'s receivers with the codec laws
(`CodecSrvProof.lean`) filled in.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.Bindings
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.CodecSrvProof

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

namespace netrpcP

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [bvi : go.BasicIntoValInj]

theorem craqArgFacts : ArgFacts where
  encString_inj := encString_inj
  encMeta_inj := encMeta_inj
  encCommitArgs_inj := encCommitArgs_inj
  encWriteArgs_inj := encWriteArgs_inj
  encClientWriteArgs_inj := encClientWriteArgs_inj
  encPropReq_inj := encPropReq_inj


theorem nodeRcv_ok (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    nodeB cfg b svc a ⊢
    craqCodec.rcv (ptrIface transport.netrpc.NodeBinding.ty b)
      (net.rpc.rcvrIs craqCodec (ptrIface transport.netrpc.NodeBinding.ty b)
        (nodeSpec cfg.γ cfg.chain a) go!"NodeBinding" false) :=
  nodeRcv craqSrvCodecLaws craqArgFacts dec_len cfg b svc a

theorem coordRcv_ok (cfg : Cfg GF) (b : Loc) (svc : GoInterface) :
    coordB cfg b svc ⊢
    craqCodec.rcv (ptrIface transport.netrpc.CoordinatorBinding.ty b)
      (net.rpc.rcvrIs craqCodec (ptrIface transport.netrpc.CoordinatorBinding.ty b)
        (coordSpec cfg.γ cfg.chain) go!"CoordinatorBinding" false) :=
  coordRcv craqSrvCodecLaws craqArgFacts dec_len cfg b svc

end proofs

end netrpcP

end github_com.despreston.go_craq

end Perennial
