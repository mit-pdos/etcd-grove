#!/usr/bin/env python3
"""Mechanical edits of a lab craq proof file for the etcd-grove port: imports, opens, section
variables. Usage: port.py SRC DST [--pkgs store.kv,store]"""
import re, sys
src, dst = sys.argv[1], sys.argv[2]
pkgs = sys.argv[3].split(',') if len(sys.argv) > 3 else []
s = open(src).read()
P = 'Dsverify.Proof.github_com.despreston.go_craq.'
s = re.sub(r'public import Craq\.Proof\.', 'public import ' + P + 'Craq.', s)
s = s.replace('public import Craq.GeneratedProof.', 'public import Dsverify.GeneratedProof.')
s = re.sub(r' NetConn Dsv dsverify_lab\.harness', '', s)
s = re.sub(r' NetConn dsverify_lab\.harness', '', s)
s = re.sub(r' dsverify_lab\.harness', '', s)
s = re.sub(r'\nattribute \[local instance\] netConnExts netConnExtsSemantics netConnExtsInterp\n  GooseGlobalGS\.gooseInvGS netConnExts_has\n',
           '\nattribute [local instance] GooseGlobalGS.gooseInvGS\n', s)
vars_ = ''.join(f' [{p}.Assumptions]' for p in pkgs)
s = s.replace('variable [go_gctx : GoGlobalContext]\n',
              'variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]\n')
s = re.sub(r'variable \[sem : go\.Semantics\] \[package_sem : examples\.craqnet\.Assumptions\]\n',
           'variable [sem : go.Semantics]' + vars_ + '\n', s)
s = s.replace('variable [net.model.Assumptions]\n', '')
open(dst, 'w').write(s)
