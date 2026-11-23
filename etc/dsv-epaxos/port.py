#!/usr/bin/env python3
"""Port dsverify-lab files (examples/epaxos/proof/<path>, e.g. Epaxos/Model/Msg.lean) into
Dsverify/Proof/github_com/imdea_software/swiftpaxos_epaxos/ by the mechanical renames
(notes/dsv-epaxos.md, "Proof port: progress"). Usage: etc/dsv-epaxos/port.py [--bufio] LABPATH...
(--bufio: also the bufio call-site rewrites of the marshal layer, `bufio_conv`.)
(LAB: the lab's proof directory, read only; DSVLAB_EPAXOS overrides it.) Hand edits after the port
are listed in the notes."""
import os, re, sys
LAB = os.environ.get('DSVLAB_EPAXOS', '/shared/dsverify-lab/examples/epaxos/proof')
DST = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
E = 'Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos'

def modmap(m):
    # lab module -> ours
    if m.startswith('Epaxos.Model.'): return E + '.Model.' + m[len('Epaxos.Model.'):]
    if m.startswith('Epaxos.Interface.'): return E + '.Interface.' + m[len('Epaxos.Interface.'):]
    if m.startswith('Epaxos.Proof.'): return E + '.' + m[len('Epaxos.Proof.'):]
    if m.startswith('Epaxos.Top.'): return E + '.Top.' + m[len('Epaxos.Top.'):]
    return m

def dstpath(p):
    m = p[:-5].replace('/', '.')
    return os.path.join(DST, modmap(m).replace('.', '/') + '.lean')

def conv(t):
    t = re.sub(r'(?m)^(public import |import )(\S+)', lambda m: m.group(1) + modmap(m.group(2)), t)
    t = re.sub(r'swiftpaxos(?![_A-Za-z0-9])', 'swiftpaxos_epaxos', t)
    t = re.sub(r'\bdsverify_lab\.harness\b', 'github_com.imdea_software.swiftpaxos_epaxos.kvs', t)
    for a in ['KvsInput', 'KvsOutput', 'Option']:
        t = t.replace(a + ' GoString', a + ' (List w8)')
    # proof files: the lab's net world (`netDistGF`, `netConnExts`) -> the part's generic GF
    t = re.sub(r'attribute \[local instance\] netConnExts netConnExtsSemantics netConnExtsInterp\s*\n\s*'
               r'GooseGlobalGS\.gooseInvGS netConnExts_has',
               'attribute [local instance] GooseGlobalGS.gooseInvGS', t)
    t = re.sub(r'variable \[GoGlobalContext\] \[hG : HeapGS \.hasLC netDistGF\] \[go\.Semantics\]',
               'variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]\n'
               'variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]', t)
    t = t.replace('variable [state.Assumptions]\n',
                  'variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]\n'
                  '  [TH : TreemapHyp GF]\n')
    t = re.sub(r'(?m)^variable \[G : GooseGlobalGS \.hasLC netDistGF\]',
               'variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]\n'
               'variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]', t)
    t = re.sub(r'\bProofMode NetConn\b', 'ProofMode Net', t)
    t = re.sub(r'(?m)^open OFE ', 'open ', t)
    t = t.replace('netDistGF', 'GF').replace('(hG := hG)', '(GF := GF)')
    t = t.replace(' Dsv github_com.', ' github_com.')
    t = re.sub(r'(?m)^(theorem \S+\.spec_holds : \S+\.spec) :=', r'\1 (GF := GF) :=', t)
    return t

def bufio_conv(t):
    # the lab harness's bufio streams -> dsv-bufio's, bundled (Interface/Marshal.lean: BufRd, BufWr)
    t = re.sub(r'\(rd : GoInterface\)\s*\(I : List w8 → IProp GF\)', '(rd : BufRd GF)', t)
    t = re.sub(r'\(wr : GoInterface\)\s*\(J Q : List w8 → IProp GF\)', '(wr : BufWr GF)', t)
    t = t.replace('bufio.ownReader br rd I', 'rdOwn br rd').replace('bufio.ownWriter bw wr J Q', 'wrOwn bw wr')
    t = re.sub(r'bufio\.readerOk rd I ∗\s*', '', t)
    t = re.sub(r'bufio\.writerOk wr J Q ∗\s*', '', t)
    t = re.sub(r'\bnextIs I ', 'nextIs rd ', t)
    t = re.sub(r'\brd I\b', 'rd', t)
    t = re.sub(r'\bwr J Q\b', 'wr', t)
    t = t.replace('#Hrd, ', '').replace('$Hrd ', '').replace('#Hwr, ', '').replace('$Hwr ', '')
    t = t.replace(', #Herr⟩', '⟩')
    t = re.sub(r'(?m)^\s*ihave #He := errOrNil_errAny .*\n', '', t)
    t = re.sub(r'(?m)^(\s*)iframe He\n', '', t)
    t = re.sub(r'net\.rpc\.errAny err ∗\s*', '', t)
    t = re.sub(r'(?<![.\w])Q \(sent ', 'wr.Q (sent ', t)
    t = t.replace('io.ExtraAssumptions', 'io.Assumptions')
    t = t.replace('bufio.io_init_of_bufio', 'EtcdGrove.bufio.io_init_of_bufio')
    return t

BUFIO = '--bufio' in sys.argv
for p in [a for a in sys.argv[1:] if a != '--bufio']:
    src = os.path.join(LAB, p)
    out = dstpath(p)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    s = conv(open(src).read())
    if BUFIO: s = bufio_conv(s)
    open(out, 'w').write(s)
    print(out[len(DST) + 1:])
