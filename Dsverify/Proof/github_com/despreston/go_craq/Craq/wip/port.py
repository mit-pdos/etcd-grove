#!/usr/bin/env python3
"""Mechanical edits of a lab craq proof file for the etcd-grove port: imports, opens, section
variables. Usage: port.py SRC DST [PKGS] [--net]
  PKGS: comma-separated packages whose `Assumptions` replace the lab's `examples.craqnet` one.
  --net: the file is over the net extension and net/rpc (opens `Net`, adds `HasExt netExt`,
  net/rpc's assumptions, `NetProtoGS`, and net/rpc's package-fact hypotheses H1)."""
import re, sys
args = [a for a in sys.argv[1:] if not a.startswith('--')]
net = '--net' in sys.argv
src, dst = args[0], args[1]
pkgs = args[2].split(',') if len(args) > 2 and args[2] else []
s = open(src).read()
P = 'Dsverify.Proof.github_com.despreston.go_craq.'
s = re.sub(r'public import Craq\.Proof\.', 'public import ' + P + 'Craq.', s)
s = s.replace('public import Craq.GeneratedProof.', 'public import Dsverify.GeneratedProof.')
s = s.replace('public import ' + P + 'Craq.Base\n', 'public import ' + P + 'Craq.Codec\npublic import ' + P + 'Craq.Hyps\n')
opn = ' Net' if net else ''
s = re.sub(r' NetConn Dsv dsverify_lab\.harness', opn, s)
s = re.sub(r' NetConn dsverify_lab\.harness', opn, s)
s = re.sub(r' NetConn Dsv\b', opn, s)
s = re.sub(r' dsverify_lab\.harness', opn, s)
s = re.sub(r'\nattribute \[local instance\] netConnExts netConnExtsSemantics netConnExtsInterp\n  GooseGlobalGS\.gooseInvGS netConnExts_has\n',
           '\nattribute [local instance] GooseGlobalGS.gooseInvGS\n', s)
ext = ' [HasExt netExt]' if net else ''
vars_ = ''.join(f' [{p}.Assumptions]' for p in pkgs)
if net:
    vars_ += '\nvariable [net.rpc.Assumptions] [π : NetProtoGS]'
s = s.replace('variable [go_gctx : GoGlobalContext]\n',
              'variable [GooseExts] [GooseSemantics] [GooseInterp]' + ext + ' [go_gctx : GoGlobalContext]\n')
s = re.sub(r'variable \[sem : go\.Semantics\] \[package_sem : examples\.craqnet\.Assumptions\]\n',
           'variable [sem : go.Semantics]' + vars_ + '\n', s)
s = s.replace('variable [net.model.Assumptions]\n', '')
s = s.replace('net.rpc.errAny', 'models_lab.errAny').replace('net.rpc.errMsg_errAny', 'errMsg_errAny')
s = s.replace('KvM.State → KvM.State → KvM.Output → IProp GF', 'KvM.Output → IProp GF')
s = re.sub(r'Q σ σ (\(\.got \(σ k\)\))', r'Q \1', s)
open(dst, 'w').write(s)
