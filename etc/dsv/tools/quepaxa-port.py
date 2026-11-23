#!/usr/bin/env python3
"""(dsv-quepaxa, a porting helper) Port lab Quepaxa/Proof files to Dsverify/Proof/raxos with the common
edits (notes/dsv-quepaxa.md): python3 etc/dsv/tools/quepaxa-port.py Smr/Step.lean ... (paths under the lab's
Quepaxa/Proof/; overwrites the destination)."""
import re, sys
LAB="/shared/dsverify-lab/examples/quepaxa/proof/Quepaxa/Proof/"
import os; DST=os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../Dsverify/Proof/raxos/")
for rel in sys.argv[1:]:
    s=open(LAB+rel).read()
    s=re.sub(r"public import Quepaxa\.Proof\.", "public import Dsverify.Proof.raxos.", s)
    s=s.replace("open Dsv in\nattribute [local instance] netConnExts netConnExtsSemantics netConnExtsInterp netConnExts_has\nopen Dsv\n","")
    s=s.replace("open Perennial.dsverify_lab.harness\n","")
    s=re.sub(r"\nopen Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode([^\n]*)\n", r"\nopen Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode\1 Net\n", s, count=1)
    s=re.sub(r"(\nvariable \{GF : BundledGFunctors\} \[G : GooseGlobalGS)", r"\nvariable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]\1", s)
    s=re.sub(r"\nvariable \[go_gctx : GoGlobalContext\]", r"\nvariable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]", s)
    s=re.sub(r"public import Quepaxa\.GeneratedProof\.", "public import Dsverify.GeneratedProof.", s)
    s=re.sub(r"public import Harness\.Proof\.(grpc|sync\.Map)[^\n]*\n", "public import Dsverify.Proof.raxos.Hyp\n", s)
    s=re.sub(r"public import Quepaxa\.Proof\.StoreInst\n", "", s)
    s=re.sub(r"(\nopen [^\n]*) NetConn\b", r"\1 Net", s)
    s=s.replace("google_golang_org.grpc.isClientConn ", "qv.grpc.isClientConn ")
    s=s.replace("open google_golang_org.protobuf.proto (codecSet kitCodecOk)\n", "open models_lab.pbcodec (PbCodec)\n")
    s=s.replace("[raxos.examples.quepaxanet.Assumptions] [net.model.Assumptions]\n", "[raxos.examples.quepaxanet.Assumptions]\n\nattribute [local instance] hyp.qpCodec\n\nvariable [gh : hyp.grpc.GrpcHyp qv.grpc]\n")
    s=re.sub(r"\nvariable \[sem : go.Semantics\]\n", "\nvariable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]\n", s)
    s=s.replace("Iris.ProofMode Net Net\n", "Iris.ProofMode Net\n")
    s=s.replace(" [net.model.Assumptions]", "")
    s=re.sub(r"\s\[(io|sync|time|strconv|fmt|sort)\.ExtraAssumptions\]", "", s)
    s=s.replace("KvInput GoString GoString","KIn").replace("KvOutput GoString","KOut")
    import os
    os.makedirs(os.path.dirname(DST+rel),exist_ok=True)
    open(DST+rel,"w").write(s)
    print("ported",rel)
