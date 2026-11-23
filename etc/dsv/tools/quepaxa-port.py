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
    s=s.replace("KvInput GoString GoString","KIn").replace("KvOutput GoString","KOut")
    import os
    os.makedirs(os.path.dirname(DST+rel),exist_ok=True)
    open(DST+rel,"w").write(s)
    print("ported",rel)
