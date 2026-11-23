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
            j = i
            while (j < len(ls) and not re.search(r':=\s*(by)?\s*$|:= by\b|:=$', ls[j]) and j - i < 25
                   and not (j > i and (not ls[j].strip() or re.match(r'^\s*\| ', ls[j])))): j += 1
            if j < len(ls) and j > i and (not ls[j].strip() or re.match(r'^\s*\| ', ls[j])): j -= 1
            blk = '\n'.join(ls[i:j + 1])
            if 'GF' not in blk:
                blk = pat.sub(lambda m: m.group(1) + ' (GF := GF)', blk, count=1)
            out.extend(blk.split('\n')); i = j + 1
        else:
            out.append(ls[i]); i += 1
    return '\n'.join(out)

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
    t = re.sub(r'attribute \[local instance\] Dsv\.netConnExts Dsv\.netConnExtsSemantics Dsv\.netConnExtsInterp\s*\n\s*'
               r'GooseGlobalGS\.gooseInvGS Dsv\.netConnExts_has',
               'attribute [local instance] GooseGlobalGS.gooseInvGS', t)
    t = t.replace('variable [GoGlobalContext] [hG : HeapGS .hasLC Dsv.GF] [go.Semantics]',
                  'variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]\n'
                  'variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]')
    t = t.replace('IProp Dsv.GF', 'IProp GF')
    t = re.sub(r'(?m)^variable \[GoGlobalContext\]$', 'variable [GooseExts] [GoGlobalContext]', t)
    # statements whose only `GF` is inside a spec's definition
    t = re.sub(r'\b((?:un)?marshalTriple) pkgInit_(\w+)', r'\1 (pkgInit_\2 (GF := GF))', t)
    t = re.sub(r'(?<![\w.])((?:epaxos|state|replica\.defs|Serializable)\.[\w.]*\.spec)(?=( MsgKind\.\w+| k\b)?\s*:= by)',
               r'\1 (GF := GF)', t)
    t = re.sub(r'(∀ k, (?:epaxos|Serializable)\.[\w.]*\.spec) k', r'\1 (GF := GF) k', t)
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
    for old, new in FIXUPS.get(p, []):
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
    s = conv(open(src).read())
    if BUFIO: s = bufio_conv(s)
    s = gf_annotate(s, gf_preds(_texts + [s]))
    s = fixup(p, s)
    open(out, 'w').write(s)
    print(out[len(DST) + 1:])
