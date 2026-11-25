#!/usr/bin/env python3
"""gen-rpcdriver-boottable: `net/rpcdriver`'s BootTable.lean, from the server command's PkgTable.lean.

  etc/gen-rpcdriver-boottable.py           write Net/Proof/.../examples/net/rpcdriver/BootTable.lean
  etc/gen-rpcdriver-boottable.py --check   write nothing; exit 1 if the committed file differs

The boot table follows the package graph of the PkgTable that etc/gen-init.py generates, which
changes with Perennial's pin (its standard-library packages' imports); rerun this after gen-init.
`--check` runs in etc/gates.sh after gen-init's.
"""
import os, re, sys
W=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CHECK='--check' in sys.argv[1:]
PKG='github_com.mit_pdos.etcd_grove.examples.net.rpcdriver'
txt=open(f'{W}/Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/rpcdriver/cmd/server/PkgTable.lean').read()
blocks=re.findall(r'  have (h\d+) : GetIsPkgInitProp pkg_id\.(\S+) \(getIsPkgInit \(GF := GF\)\) := by\n    refine And\.intro \?_ \?_\n    · rfl\n    exact (.*)\n', txt)
names={h:q for h,q,_ in blocks}
chain=[]
for h,q,ex in blocks:
    if q.startswith(f'{PKG}.cmd.'): continue
    chain.append((q,[names[c] for c in re.findall(r'\bh\d+\b', ex)]))
closure={}
for q,cs in chain:
    s={q}
    for c in cs: s|=closure[c]
    closure[q]=s
owned=[PKG,'net.rpc','net.http']
free=[q for q,_ in chain if not (closure[q]&set(owned))]
def wfname(q): return q.replace('«','').replace('»','').replace('.','_')
def tup(k): return f'⟨{k}True.intro⟩' if k else 'True.intro'
o=[]
o.append('''/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: the package facts of its machines' first initialization

The tables of a machine's boot (as the dsverify kits', `etc/dsv/kitgen.py`'s `BootTable.lean`; written by
`etc/gen-rpcdriver-boottable.py` from the server command's `PkgTable.lean`, both commands having the same closure): generic in
a program's table `G` that gives every package of `rpcdriver`'s import closure its `isPkgInit`
(`KitG G`), the facts at `G` (`wf_*`) and, for the packages whose closure avoids the owned packages
(`ownedPkgs`: `rpcdriver`, net/rpc, net/http, whose first initializations return the machine's owned
resources), at `gOff S G` for `S` a sub-list of `ownedPkgs` (`wfO_*`): the table in which the packages
of `S` are not initialized yet.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.server.PkgTable

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

namespace Perennial
''')
o.append(f'namespace {PKG}\n')
o.append('open Iris Iris.BI Iris.ProgramLogic Iris.Std\n')
o.append('section table\nvariable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]\nvariable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]\nvariable [package_sem : Assumptions]\n')
o.append('''/-- The table `G` with the packages of `S` not initialized (their entry `False`). -/
def gOff (S : List GoString) (G : GoString → IProp GF) : GoString → IProp GF := fun p =>
  if p ∈ S then iprop(False) else G p

theorem gOff_ne (S : List GoString) (G : GoString → IProp GF) (p : GoString) (h : p ∉ S) :
    gOff S G p = G p := by
  unfold gOff; rw [if_neg h]

theorem gOff_off (S : List GoString) (G : GoString → IProp GF) (p : GoString) (h : p ∈ S) :
    gOff S G p ⊢ iprop(False) := by
  unfold gOff; rw [if_pos h]

theorem gOff_sub (S S' : List GoString) (G : GoString → IProp GF) (h : ∀ q ∈ S', q ∈ S)
    (p : GoString) : gOff S G p ⊢ gOff S' G p := by
  unfold gOff
  by_cases h' : p ∈ S'
  · rw [if_pos (h p h'), if_pos h']
  · rw [if_neg h']
    split
    · exact false_elim
    · exact .rfl

theorem gOff_nil (G : GoString → IProp GF) : gOff [] G = G := by
  funext p; unfold gOff; simp
''')
o.append("/-- The owned packages (the file header). -/\ndef ownedPkgs : List GoString :=\n  ["+', '.join(f'pkg_id.{q}' for q in owned)+"]\n")
o.append("/-- A program's table gives every package of `rpcdriver`'s import closure its fact. -/\nstructure KitG (G : GoString → IProp GF) : Prop where")
for q,_ in chain: o.append(f'  e_{wfname(q)} : G pkg_id.{q} = isPkgInit (PROP := IProp GF) pkg_id.{q}')
o.append('')
for q,cs in chain:
    k=''.join(f'wf_{wfname(c)} h, ' for c in cs)
    o.append(f'theorem wf_{wfname(q)} {{G : GoString → IProp GF}} (h : KitG G) :\n    GetIsPkgInitProp pkg_id.{q} G :=\n  And.intro h.e_{wfname(q)} {tup(k)}\n')
for q,cs in chain:
    if q not in free: continue
    k=''.join(f'wfO_{wfname(c)} h S hS, ' for c in cs)
    o.append(f'theorem wfO_{wfname(q)} {{G : GoString → IProp GF}} (h : KitG G) (S : List GoString)\n    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.{q} (gOff S G) :=\n  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.{q} ∉ ownedPkgs) (hS _ hm))).trans\n    h.e_{wfname(q)}) {tup(k)}\n')
for q,cs in chain:
    if q != 'net.http': continue
    k=''.join(f'wfO_{wfname(c)} h S hS, ' for c in cs)
    o.append(f'/-- net/http\'s facts at a table in which it is initialized (its imports avoid the owned packages). -/\ntheorem wfX_{wfname(q)} {{G : GoString → IProp GF}} (h : KitG G) (S : List GoString)\n    (hS : ∀ q ∈ S, q ∈ ownedPkgs) (hn : pkg_id.{q} ∉ S) : GetIsPkgInitProp pkg_id.{q} (gOff S G) :=\n  And.intro ((gOff_ne S G _ hn).trans h.e_{wfname(q)}) {tup(k)}\n')
o.append('end table\n')
o.append(f'end {PKG}\nend Perennial\n')
OUT=f'{W}/Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/rpcdriver/BootTable.lean'
text='\n'.join(o)
if CHECK:
    cur=open(OUT).read() if os.path.exists(OUT) else None
    if cur!=text:
        sys.exit('gen-rpcdriver-boottable: BootTable.lean differs (run etc/gen-rpcdriver-boottable.py)')
    print('gen-rpcdriver-boottable: ok')
else:
    open(OUT,'w').write(text)
    print('gen-rpcdriver-boottable: wrote', os.path.relpath(OUT, W), f'({len(chain)} packages, {len(free)} outside the owned closure)')
