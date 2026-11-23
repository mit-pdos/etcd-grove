#!/usr/bin/env python3
"""Port dsverify-lab files (examples/epaxos/proof/<path>, e.g. Epaxos/Model/Msg.lean) into
Dsverify/Proof/github_com/imdea_software/swiftpaxos_epaxos/ by the mechanical renames
(notes/dsv-epaxos.md, "Proof port: progress"). Usage: etc/dsv-epaxos/port.py [--bufio] LABPATH...
(--bufio: also the bufio call-site rewrites of the marshal layer, `bufio_conv`.)
Hand-maintained after their port (do not re-port; notes/dsv-epaxos.md): Interface/Marshal.lean,
wire/{WProg,RProg,Link}.lean, wire/Varint/{ReadUvarint,ReadVarint}.lean,
Interface/{Replica,ReplicaSpec}.lean, replica/{PrefixReader,SendMsg,ReplyPropose}.lean. Every other ported file is
`port.py`'s output (with `FIXUPS`).
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
    if m.startswith('Epaxos.GeneratedProof.'): return 'Dsverify.GeneratedProof.' + m[len('Epaxos.GeneratedProof.'):]
    if m.startswith('Epaxos.Code.'): return 'Dsverify.Code.' + m[len('Epaxos.Code.'):]
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
    t = re.sub(r'(?m)^variable \[GoGlobalContext\] \[G : GooseGlobalGS \.hasLC netDistGF\]',
               'variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]\n'
               'variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]', t)
    t = re.sub(r'(?m)^variable \[GoGlobalContext\] \[hG : HeapGS \.hasLC netDistGF\]$',
               'variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]\n'
               'variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]', t)
    t = re.sub(r'(?m)^variable \[G : GooseGlobalGS \.hasLC netDistGF\]',
               'variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]\n'
               'variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]', t)
    t = re.sub(r'\bProofMode NetConn\b', 'ProofMode Net', t)
    t = re.sub(r'(?m)^open OFE ', 'open ', t)
    t = re.sub(r'(?m)^attribute \[local instance\] netConnExts netConnExtsSemantics netConnExtsInterp\n',
               'variable [GooseExts]\n', t)
    t = re.sub(r'\bkit\.pre\b', 'inPre', t)
    # sealed definitions' unseal equations: `@X (GF := GF) = @XDef` (now with more instance args)
    t = re.sub(r'@(\w+) \(GF := GF\) = @(\w+)', r'\1 (GF := GF) = \2', t)
    t = re.sub(r'@(\w+) \(hG := hG\) = @(\w+)', r'\1 (GF := GF) = \2', t)
    # the lab's protocol namespace was disjoint from its `clientN`; here it is inside `epEop`
    t = t.replace('''theorem protoN_clientN_disj : (↑protoN : CoPset) ## ↑clientN := by
  unfold protoN epN clientN; solve_ndisj''', '''theorem protoN_epEop : (↑protoN : CoPset) ⊆ epEop := by
  unfold protoN epEop; exact nclose_subseteq _ _''')
    t = t.replace('''theorem protoN_escrowN_disj : (↑protoN : CoPset) ## ↑escrowN := by
  unfold protoN escrowN; solve_ndisj''', '''theorem protoN_escrowN_disj : (↑protoN : CoPset) ## ↑escrowN := by
  unfold protoN escrowN; exact ndot_ne_disjoint _ (by decide)''')
    t = t.replace('protoN_clientN_disj', 'protoN_epEop')
    t = re.sub(r'(?m)^((?:def|theorem) \S+) \[GoGlobalContext\]',
               lambda m: m.group(0) if 'variable [GooseExts]' in t[:m.start()]
               else m.group(1) + ' [GooseExts] [GoGlobalContext]', t)
    t = t.replace('netDistGF', 'GF').replace('(hG := hG)', '(GF := GF)')
    t = t.replace(' Dsv github_com.', ' github_com.')
    # connection ids: the lab's net model's `w64`, `Net/`'s `Nat` (Model/State.lean `Proposal.cid`)
    t = re.sub(r'\((cid\w*) : w64\)', r'(\1 : Nat)', t)
    t = t.replace('GMap w64 KvO', 'GMap Nat KvO').replace('(fd : w64 → Option KvO)', '(fd : Nat → Option KvO)').replace('(cid c : w64)', '(cid : Nat) (c : w64)')
    # the escrow fires under remote's mask `⊤ ∖ epEop` (Interface/Client.lean), not the lab's `clientN`
    t = t.replace('(hEc : ↑clientN ⊆ E)', '(hEc : ⊤ \\ epEop ⊆ E)')
    t = t.replace('(hNc : (↑N : CoPset) ## ↑clientN)', '(hNc : (↑N : CoPset) ⊆ epEop)')
    t = t.replace('''have hEc' : ↑clientN ⊆ E \\ ↑N := fun q hq =>
      CoPset.in_diff.2 ⟨hEc q hq, fun h => hNc q ⟨h, hq⟩⟩''', '''have hEc' : ⊤ \\ epEop ⊆ E \\ ↑N := fun q hq =>
      CoPset.in_diff.2 ⟨hEc q hq, fun h => (CoPset.in_diff.1 hq).2 (hNc q h)⟩''')
    t = re.sub(r'(?m)^(theorem \S+\.spec_holds : \S+\.spec) :=', r'\1 (GF := GF) :=', t)
    return t

PROOF = os.path.join(DST, E.replace('.', '/'))

def gf_preds(texts):
    # names defined `def X … : IProp GF :=` (GF implicit in them)
    names = set()
    for s in texts:
        for m in re.finditer(r'(?m)^(?:@\[[^\]]*\]\s*)?(?:noncomputable )?(?:abbrev|def) ([\w.]+)', s):
            k = s.find(':=', m.end())
            if k < 0 or k - m.end() > 600: continue
            if re.search(r':\s*IProp GF\s*$', s[m.end():k]): names.add(m.group(1))
    return names

def gf_annotate(t, names):
    # a statement whose only `GF` is inside one of `names`: annotate its first use
    if not names: return t
    pat = re.compile(r'(?<![\w.])(' + '|'.join(sorted((re.escape(n) for n in names), key=len, reverse=True)) + r')(?![\w.])')
    out = []; ls = t.split('\n'); i = 0
    while i < len(ls):
        if re.match(r'^(theorem|instance|lemma) ', ls[i]):
            # the statement ends at the first `:=` outside brackets (or a `|` alternative)
            j = i; depth = 0; done = False
            while j < len(ls) and j - i < 30 and not done:
                if j > i and (not ls[j].strip() or re.match(r'^\s*\| ', ls[j])): j -= 1; break
                l = ls[j]; k = 0
                while k < len(l):
                    c = l[k]
                    if c in '([{⟨': depth += 1
                    elif c in ')]}⟩': depth -= 1
                    elif l.startswith(':=', k) and depth <= 0: done = True; break
                    k += 1
                if not done: j += 1
            blk = '\n'.join(ls[i:j + 1])
            if 'GF' not in blk:
                blk = pat.sub(lambda m: m.group(1) + ' (GF := GF)', blk, count=1)
            out.extend(blk.split('\n')); i = j + 1
        else:
            out.append(ls[i]); i += 1
    return '\n'.join(out)

def generic_conv(t):
    # rules every port needs (after `conv`)
    # the lab's net model's assumptions -> `Net/`'s extension and protocol world; the store's
    # assumptions and gods' treemap hypothesis alongside (unused ones are not included)
    # (`TreemapHyp GF` only where the store is used: a section instance whose dependencies are
    # included is included in every declaration that mentions `GF`)
    TS = ('\nvariable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]'
          ' [TH : TreemapHyp GF]') if 'isState' in t else ''
    t = re.sub(r'(?m)^(variable \[.*)\[net\.model\.Assumptions\](.*)$',
               lambda m: m.group(1) + '[HasExt netExt] [π : NetProtoGS]' + m.group(2) + TS, t)
    t = t.replace('[io.ExtraAssumptions]', '[io.Assumptions]')
    # `have h := thm γ …` (no expected type): nothing determines the theorem's `GF`
    t = re.sub(r'(have \w+ := )(?!outOkB_of_toks)([a-zA-Z][\w.]*) γ ', r'\1\2 (GF := GF) γ ', t)
    # a spec taken as a hypothesis: its `GF` is not determined by anything else
    t = re.sub(r'\) : ([\w.]+\.spec) := by', r') : \1 (GF := GF) := by', t)
    t = re.sub(r'\((h\w* : [\w.]+\.spec)\)', r'(\1 (GF := GF))', t)
    t = re.sub(r'attribute \[local instance\] Dsv\.netConnExts Dsv\.netConnExtsSemantics Dsv\.netConnExtsInterp\s*\n\s*'
               r'GooseGlobalGS\.gooseInvGS Dsv\.netConnExts_has',
               'attribute [local instance] GooseGlobalGS.gooseInvGS', t)
    t = t.replace('variable [GoGlobalContext] [hG : HeapGS .hasLC Dsv.GF] [go.Semantics]',
                  'variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]\n'
                  'variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]')
    t = t.replace('IProp Dsv.GF', 'IProp GF')
    t = re.sub(r'(?m)^variable \[GoGlobalContext\]$',
               lambda m: m.group(0) if 'variable [GooseExts]' in t[:m.start()]
               else 'variable [GooseExts] [GoGlobalContext]', t)
    t = re.sub(r'(?m)^(theorem \S+\.(?:wp_proof|spec_holds) : \S+\.spec) :=', r'\1 (GF := GF) :=', t)
    # statements whose only `GF` is inside a spec's definition
    t = re.sub(r'\b((?:un)?marshalTriple) pkgInit_(\w+)', r'\1 (pkgInit_\2 (GF := GF))', t)
    t = re.sub(r'(?<![\w.])((?:epaxos|state|replica\.defs|Serializable)\.[\w.]*\.spec)(?=( MsgKind\.\w+| k\b)?\s*:= by)',
               r'\1 (GF := GF)', t)
    t = re.sub(r'(∀ k, (?:epaxos|Serializable)\.[\w.]*\.spec) k', r'\1 (GF := GF) k', t)
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
    t = t.replace(' Hwr Hw ', ' Hw ').replace('iframe Hwr ', 'iframe ')
    t = t.replace('#Hrd, ', '').replace('$Hrd ', '').replace('#Hwr, ', '').replace('$Hwr ', '')
    t = re.sub(r', #Herr\d*⟩', '⟩', t)
    t = re.sub(r'(%he\d*), #He\d*, ', r'\1, ', t)
    t = re.sub(r'(?m)^\s*ihave #He := errOrNil_errAny .*\n', '', t)
    t = re.sub(r'(?m)^(\s*)iframe He\d*\n', '', t)
    t = re.sub(r'net\.rpc\.errAny err ∗\s*', '', t)
    t = re.sub(r'(?<![.\w])Q \(sent ', 'wr.Q (sent ', t)
    t = t.replace('io.ExtraAssumptions', 'io.Assumptions')
    t = t.replace('bufio.io_init_of_bufio', 'EtcdGrove.bufio.io_init_of_bufio')
    t = re.sub(r'\bnextIs_(total|shift) I ', r'nextIs_\1 rd ', t)
    t = re.sub(r'wprog_finish _ _ _ _ _ _ _ _ _ ', 'wprog_finish _ _ _ _ _ _ _ ', t)
    t = re.sub(r'wprog_start _ _ _ _ _ _ _ _ ', 'wprog_start _ _ _ _ _ _ ', t)
    # the stream fact comes a step later (`nextIs_read`): strip it with `imod` after the `ihave`
    ls = t.split('\n'); out = []; i = 0
    while i < len(ls):
        l = ls[i]
        m = re.match(r'^(\s*)ihave ⟨(\w+), %(\w+)⟩ := nextIs_read', l)
        if not m:
            out.append(l); i += 1; continue
        ind, h = m.group(1), m.group(3)
        out.append(l.replace('%' + h + '⟩', h + '⟩', 1)); i += 1
        while i < len(ls) and ls[i].strip() and (len(ls[i]) - len(ls[i].lstrip()) > len(ind)
                or ls[i].lstrip().startswith('· ')) :
            out.append(ls[i]); i += 1
        out.append(ind + 'imod ' + h + ' with %' + h)
    return '\n'.join(out)

# hand fixes after the mechanical port, by lab path: (old, new) replacements, each must apply
FIXUPS = {
    'Epaxos/Proof/replica/Stream.lean': [
        # a connection's reader is `connRd` (Interface/ConnBuf): its stream fact is
        # `▷ protoPrefix`, bufio's `ownBufReader_fact` (the lab's `ownReader_proto` is not needed)
        ('/-- A buffered reader over a connection', '/-- What the unmarshalers need', ''),
        ("""    (side : Bool) (cid : Nat) (dl : Nat) (hdl : dl = dialerOf id j side) (hd : dl < 5)
    (ws : List Msg)""", """    (side : Bool) (cid : Nat) (t : Loc) (eof la ra ed : GoInterface) (dl : Nat)
    (hdl : dl = dialerOf id j side) (hd : dl < 5) (ws : List Msg)"""),
        ("""      nextIs (recvTok cid side (peerPin γ id L j side))""", """      nextIs (connRd t cid side eof la ra ed (peerPin γ id L j side))"""),
        ("""  iintro %S HI
  ihave ⟨HI, #Hp⟩ := recvTok_proto $$ HI
  iframe HI
  by_cases hS""", """  iintro %S #Hp
  simp only [connRd]
  inext
  by_cases hS"""),
    ],
    'Epaxos/Proof/epaxos/GhostSend.lean': [
        # `S'` is a `let`: the lab's `iframe` closed `kvHalf γ S'.kv` by unification, ours does not
        ('''    isplitr; · ipureintro; exact InvX_rep_eq hX rfl rfl
    iframe
  imodintro
  iframe Hh''', '''    isplitr; · ipureintro; exact InvX_rep_eq hX rfl rfl
    iframe
    rw [show S'.kv = S.kv from rfl]; iexact Hkv
  imodintro
  iframe Hh'''),
    ],
    'Epaxos/Interface/Registry.lean': [
        # the kit's deployment (`examples/epaxosnet/kit.go`), not the lab harness's 10.77.0.x nodes
        ('''* **The addresses** of the deployment''', '''* **The final node list**''', '''* **The addresses** of the deployment (`ServerAddrs()`, `examples/epaxosnet/kit.go`):
  server `k` (`Server(k)`; k = 1 the master, 2..6 the replicas) is at `127.0.0.1:(7500+k)`;
  replica `k` registers `("127.0.0.1", 7500 + k)`, i.e. its peer/client address `peerAddrOf k`
  (`serverAddrs[k - 1]`), and serves rpc on `rpcAddrOf k` (`127.0.0.1:(8500+k)`); the master is
  `masterAddr` (`127.0.0.1:7501`, listening on the wildcard `":7501"`).
'''),
        ('''/-! ## The addresses -/''', '''/-- A final node list''', '''/-! ## The addresses -/

/-- The replica servers (`Server(k)`). -/
def replicaNodes : List Nat := [2, 3, 4, 5, 6]

/-- The master's address (server 1's). -/
def masterAddr : GoString := go!"127.0.0.1:7501"

/-- The servers' IP (`host(addrs[id-1])`, what `serve` passes to `register`). -/
def masterIp : GoString := go!"127.0.0.1"

theorem masterAddr_eq : masterAddr = masterIp ++ go!":" ++ go!"7501" := rfl

theorem masterAddr_server : serverAddrs[0]? = some masterAddr := rfl

/-- Replica `k`'s IP (`host(addrs[k-1])`). -/
def replicaIp (_k : Nat) : GoString := go!"127.0.0.1"

/-- Replica `k`'s peer/client address (`ServerAddrs()[k - 1]`, port `7500 + k`): what it
registers with the master and what its peers and clients dial. -/
def peerAddrOf (k : Nat) : GoString := serverAddrs.getD (k - 1) []

/-- Replica `k`'s rpc address (`ip:(port + 1000)`, `serve`). -/
def rpcAddrOf (k : Nat) : GoString := replicaIp k ++ go!":" ++ fmt.decimal (8500 + k)

/-- The replicas' rpc addresses. -/
def replicaRpcAddrs : List GoString := replicaNodes.map rpcAddrOf

theorem replicaAddrs_eq : replicaAddrs = replicaNodes.map peerAddrOf := by decide

/-- What `Register` formats (`fmt.Sprintf("%s:%d", Addr, Port)`) for node `k`'s arguments is
its peer address. -/
theorem peerAddrOf_fmt (k : Nat) (hk : k ∈ replicaNodes) :
    peerAddrOf k = replicaIp k ++ go!":" ++ fmt.decimal (7500 + k) := by
  simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    simp [fmt.decimal, fmt.decimalNat_of_ge, fmt.decimalNat_of_lt, fmt.digitByte, peerAddrOf,
      replicaIp, serverAddrs]

theorem peerAddrOf_inj (k k' : Nat) (hk : k ∈ replicaNodes) (hk' : k' ∈ replicaNodes)
    (h : peerAddrOf k = peerAddrOf k') : k = k' := by
  simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, or_false] at hk hk'
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert h; decide)

'''),
    ],
    'Epaxos/Proof/replica/Ghost.lean': [
        # connections are `Net/`'s (`connAt`, Interface/ConnBuf: `connWr`/`connRd`), not the lab
        # harness's `net.rpc.connIface` and `bufio.ownWriter`/`ownReader`
        ('public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.RpcTable',
         'public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.RpcTable\n'
         'public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.ConnBuf'),
                ('''/-- The dialer of a connection''', '''theorem peerPX_ppc (γ : EpNames) (id : Nat) (L : List GoString) (j : Nat) (side : Bool) :
    ProtoPrefixClosed (peerPX (GF := GF) γ id L j side) := by
  unfold peerPX; split
  · exact repAccP_ppc γ _
  · exact repDialP_ppc γ _

/-- The end `side` of connection `cid` is the `*TCPConn` in `c` (`net.connAt`, some addresses),
with `ErrDeadlineExceeded`'s and `io.EOF`'s values (its errors' evidence). -/
def connIn (c : GoInterface) (cid : Nat) (side : Bool) (t : Loc) (la ra ed eof : GoInterface) :
    IProp GF :=
  iprop(⌜c = interface.ok (net.connIface t)⌝ ∗ (∃ a : GoString, net.connAt t cid side a la ra) ∗
    globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ globalAddr io.EOF ↦□ eof)

instance connIn_persistent (c : GoInterface) (cid : Nat) (side : Bool) (t : Loc)
    (la ra ed eof : GoInterface) : Persistent (connIn (GF := GF) c cid side t la ra ed eof) := by
  unfold connIn; infer_instance

/-- The dialer of a connection'''),
        ('''  iprop(∃ (sent pend : List w8) (err : GoInterface) (ws : List Msg),
    net.rpc.connIface c cid side ∗''', '''  iprop(∃ (sent pend : List w8) (err : GoInterface) (ws : List Msg) (t : Loc)
      (la ra ed eof : GoInterface),
    connIn c cid side t la ra ed eof ∗'''),
        ('''    bufio.ownWriter w c (sendTok cid side (peerPX γ id L j side))
      (peerPX γ id L j side cid) sent pend err ∗''', '''    wrOwn w (connWr t cid side la ra ed (peerPX γ id L j side) (peerPX_ppc γ id L j side) 4096)
      sent pend err ∗'''),
        ('''  iprop(net.rpc.connIface c cid side ∗ ⌜if side then id < j else j < id⌝ ∗''',
         '''  iprop(∃ (t : Loc) (la ra ed eof : GoInterface), connIn c cid side t la ra ed eof ∗
    ⌜if side then id < j else j < id⌝ ∗'''),
        ('''    bufio.ownReader rd c (recvTok cid side (peerPin γ id L j side))
      (streamHdr (dialerOf id j side) (!side)) ∗''', '''    rdOwn rd (connRd t cid side eof la ra ed (peerPin γ id L j side))
      (streamHdr (dialerOf id j side) (!side)) ∗'''),
        ('''  iprop(∃ (c : GoInterface) (sent pend : List w8) (err : GoInterface),
    net.rpc.connIface c cid true ∗
    bufio.ownWriter w c (sendTok cid true (repAccP γ (L.getD id []))) (repAccP γ (L.getD id []) cid)
      sent pend err ∗''', '''  iprop(∃ (c : GoInterface) (sent pend : List w8) (err : GoInterface) (t : Loc)
      (la ra ed eof : GoInterface),
    connIn c cid true t la ra ed eof ∗
    wrOwn w (connWr t cid true la ra ed (repAccP γ (L.getD id [])) (repAccP_ppc γ _) 4096)
      sent pend err ∗'''),
    ],
    'Epaxos/Interface/EpaxosGhost.lean': [
        ('have : ∀ o, outOk γ i o = outOkB γ i o', 'have : ∀ o, outOk (GF := GF) γ i o = outOkB γ i o'),
    ],
    'Epaxos/Proof/epaxos/GhostExec.lean': [
        # `iinv`'s side-condition solver (`simp [*]`) loops on `hw`/`hidx` here: hide them across it
        ('''theorem ep_execCmdB''', '''/-- A fact hidden from `simp [*]` (`iinv`'s side-condition solver). -/
@[irreducible] def hideP (P : Prop) : Prop := P

theorem ep_execCmdB'''),
        ('''  icases Hlc with ⟨Hlc1, Hlc2⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \\ ↑N) $$ Hlc1 Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, ⟨%F, HF, %hF, Hfm⟩, Hsents, Hdel, Hops⟩''', '''  icases Hlc with ⟨Hlc1, Hlc2⟩
  have hk : hideP (σ.inst x = some w ∧ idx < (w.cmds.getD []).length ∧ ↑escrowN ⊆ E ∧
      (↑N : CoPset) ## ↑escrowN) := by
    unfold hideP; exact ⟨hw, hidx, hEe, hNe⟩
  clear hw hidx hEe hNe
  iinv Hinv with Hi Hclose
  obtain ⟨hw, hidx, hEe, hNe⟩ : σ.inst x = some w ∧ idx < (w.cmds.getD []).length ∧
      ↑escrowN ⊆ E ∧ (↑N : CoPset) ## ↑escrowN := by
    unfold hideP at hk; exact hk
  imod lc_fupd_elim_later (E := E \\ ↑N) $$ Hlc1 Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, ⟨%F, HF, %hF, Hfm⟩, Hsents, Hdel, Hops⟩'''),
    ],
}

def fixup(p, s):
    for fx in FIXUPS.get(p, []):
        if len(fx) == 3:  # (start, end, new): replace the span from `start` up to `end`
            a, b, new = fx
            i = s.index(a); j = s.index(b, i)
            s = s[:i] + new + s[j:]
            continue
        old, new = fx
        assert old in s, (p, old[:60])
        s = s.replace(old, new, 1)
    return s

BUFIO = '--bufio' in sys.argv
_texts = []
for root, _, fs in os.walk(PROOF):
    for x in fs:
        if x.endswith('.lean'): _texts.append(open(os.path.join(root, x)).read())
for p in [a for a in sys.argv[1:] if a != '--bufio']:
    src = os.path.join(LAB, p)
    out = dstpath(p)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    s = generic_conv(conv(open(src).read()))
    if BUFIO: s = bufio_conv(s)
    s = gf_annotate(s, gf_preds(_texts + [s]))
    # sealed definitions' unseal equations (`@X = @XDef`; more instance arguments here)
    s = re.sub(r'(_unseal : )@(\w+)(?: \(GF := GF\))? = @(\w+)', r'\1\2 (GF := GF) = \3', s)
    s = fixup(p, s)
    # the lab harness's `net.rpc.connIface c cn s` is `connIf` (Interface/ConnBuf.lean)
    s = s.replace('net.rpc.connIface', 'connIf')
    open(out, 'w').write(s)
    print(out[len(DST) + 1:])
