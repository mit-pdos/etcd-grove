"""The paxos kit (notes/dsv-paxos.md): its etc/goose.py project and its etc/gen-init.py
configuration, in the format of etc/dsv/README.md."""
import os

# etc/goose.py's project dsv-paxos (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-paxos",
    # dsverify-lab's paxos kit (notes/dsv-paxos.md; notes/dsverify-net-port-plan.md, phase 6):
    # the lab's fork of xiang90/paxos (examples/paxos/fork/paxos at lab master 7a84fb35) with
    # its kit ported onto examples/lib/remote, `examples/dsverify/paxos` (a Go module of its
    # own, module path the fork's). Into the part `Dsverify/` (modules `Dsverify.*`), with
    # remote and `net` the part `Net/`'s, lintest and porcupine the main tree's, marshal
    # Perennial's.
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "paxos"),
    root="Dsverify",
    lean_roots=["github.com/xiang90/paxos=Dsverify",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall="],
    packages=[".", "./examples/paxosnet", "./examples/paxosnet/cmd/orch"]
             + ["./examples/paxosnet/cmd/client%d" % c for c in range(4)]
             + ["./examples/paxosnet/cmd/server%d" % s for s in range(1, 6)],
    owned=[os.path.join("github_com", "xiang90")],
)

# etc/gen-init.py: the packages whose `Init.lean` is generated into `Dsverify/Proof/`, and the
# programs whose `PkgTable.lean` is
PAXOS = 'github_com.xiang90.paxos'
NODES = ['orch'] + [f'client{c}' for c in range(4)] + [f'server{s}' for s in range(1, 6)]
PKGS = [PAXOS, f'{PAXOS}.examples.paxosnet'] + [f'{PAXOS}.examples.paxosnet.cmd.{n}' for n in NODES]
PROGRAMS = {f'{PAXOS}.examples.paxosnet.cmd.{n}':
            f'Proof/{PAXOS.replace(".", "/")}/examples/paxosnet/cmd/{n}/PkgTable.lean'
            for n in NODES}

# etc/dsv/kitgen.py: the kit's generated plumbing (notes/dsv-kitgen.md): the commands' mains, the
# statement, its definitions and proof, the commands' `wp_main`s. Templates: `{n}` a machine's
# command, `{id}` its Go id, `{i}` its index in `system`, `{pkg}` the kit package's namespace.
_MAINS_VARS = '''variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.{n}.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]'''

_KP = '''  ihave #Hkp : (isPkgInit (PROP := IProp GF) pkg_id.{pkg}) $$ []
  · iPkgInit
  (try wp_auto)'''

KITGEN = dict(
    name='paxos',
    go_module_dir=os.path.join('examples', 'dsverify', 'paxos'),
    go_pkg_dir=os.path.join('examples', 'paxosnet'),
    go_import='github.com/xiang90/paxos/examples/paxosnet',
    go_pkg='paxosnet',
    lean_pkg=f'{PAXOS}.examples.paxosnet',
    # the kit's own Lean (Dsverify/{Proof,Spec}/<root>/): never exported (--export-challenge)
    proof_roots=[PAXOS],
    # the opening prompt's sentences about the system (etc/dsv/challenge-prompt.txt)
    prompt=dict(system="a Paxos deployment over Go's net",
                check="whose driver runs a linearizability check of the clients' history"),
    roles=[
        dict(cmd='orch', go_doc="the paxos kit's orchestrator machine", go_call='Orch()',
             share='([∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (woR Γ) a) ∗ mapCtx (Gg := G) (I := BStr) ∗ '
                   'pendCtx (Gg := G) (woR Γ) (woS0 (GF := remoteGF)) γp ∗ '
                   'pendLib (Gg := G) (woS0 (GF := remoteGF)) γp (woS0 (GF := remoteGF)).M.init ∗ '
                   '[∗list] a ∈ clientAddrs, budUnits (Gg := G) a 3',
             intro='⟨#Has, #Hmap0, #Hpend0, Hlib0, Hbud0⟩', main='cmd.{n}.wp_main wp_Orch Γ γp hrb',
             frame='Hlib0 Hbud0', split='Hlib Hbud',
             wp_main='''theorem wp_main (wp_Orch : paxosnet.Orch.spec (GF := GF) (hG := hG)) (Γ : Names)
    (γp : PendNames) (hrb : receiptBound GF ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.{pkg}.cmd.{n} ∗
        ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (woR Γ) a) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := BStr) ∗
        pendCtx (Gg := hG.goose_globalGS) (woR Γ) (woS0 (GF := GF)) γp ∗
        pendLib (Gg := hG.goose_globalGS) (woS0 (GF := GF)) γp (woS0 (GF := GF)).M.init ∗
        [∗list] a ∈ clientAddrs, budUnits (Gg := hG.goose_globalGS) a 3 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Has, #Hmap, #Hpend, Hlib, Hbud⟩
''' + _KP + '''
  wp_apply wp_Orch Γ γp hrb $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
  iapply HΦ
  itrivial'''),
        dict(cmd='client{id}', ids=list(range(4)), go_doc="the paxos kit's client machine {id}",
             go_call='Client({id})',
             share='isPaxos Γ ∗ allProtos Γ ∗ clientTok Γ (W64 {id}) ∗ '
                   'remoteAddr (Gg := G) (woR Γ) (clientAddrs.getD {id} []) ∗ mapCtx (Gg := G) (I := BStr)',
             intro='⟨#Hpx0, #Hprotos0, Htok0, #Hra0, #Hmap0⟩', main='cmd.{n}.wp_main wp_Client Γ',
             frame='Htok0', split='Htok{id}', split_pre='unfold clientTok',
             wp_main='''theorem wp_main (wp_Client : paxosnet.Client.spec (GF := GF) (hG := hG)) (Γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.{pkg}.cmd.{n} ∗ isPaxos Γ ∗ allProtos Γ ∗
        clientTok Γ (W64 {id}) ∗
        remoteAddr (Gg := hG.goose_globalGS) (woR Γ) (clientAddrs.getD {id} []) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := BStr) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpx, #Hprotos, Htok, #Hra, #Hmap⟩
''' + _KP + '''
  wp_apply wp_Client Γ (W64 {id}) (by decide) $$ [Htok] as %hf
  · rw [show uint.nat (W64 {id}) = {id} from rfl]
    iframe #
    iframe Htok
  exact hf.elim'''),
        dict(cmd='server{id}', ids=list(range(1, 6)), go_doc="the paxos kit's server machine {id}",
             go_call='Server({id})',
             share='isPaxos Γ ∗ allProtos Γ ∗ (if uint.nat (W64 {id}) ≤ 3 then stOwn Γ (W64 {id}) AccState.init else True)',
             intro='⟨#Hpx0, #Hprotos0, Hst0⟩', main='cmd.{n}.wp_main wp_Server Γ', frame='Hst0',
             # servers 1..3 are the acceptors (their state is the share), 4..5 the learners
             split=lambda m: f'Hst{m.id}' if m.id <= 3 else '',
             split_pre=lambda m: 'rw [if_pos (by decide)]' if m.id <= 3 else 'rw [if_neg (by decide)]',
             wp_main='''theorem wp_main (wp_Server : paxosnet.Server.spec (GF := GF) (hG := hG)) (Γ : Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.{pkg}.cmd.{n} ∗ isPaxos Γ ∗ allProtos Γ ∗
        (if uint.nat (W64 {id}) ≤ 3 then stOwn Γ (W64 {id}) AccState.init else True) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpx, #Hprotos, Hst⟩
''' + _KP + '''
  wp_apply wp_Server Γ (W64 {id}) (by decide) $$ [Hst] as %hf
  · iframe #
    iframe Hst
  exact hf.elim'''),
    ],
    statement=dict(
        theorem='paxos_remote_robust',
        doc='''**The paxos kit, closed** (dsverify-lab's paxos-net-3 on examples/lib/remote; notes/dsv-paxos.md):
ten machines, none of which crashes -- the orchestrator (`remote.Check` of four clients' proposals
against the write-once register with pending proposals), four client machines (each
`remote.ServeClient`, its operation the client's proposal over its own paxos node) and five servers
(three acceptors, two learners; xiang90/paxos over TCP) -- deployed at `paxosKitAddrs` (`DistDeploy`:
the addresses distinct and valid, no connection, no listener). In every execution of fewer than `remoteStepBound` (`2 ^ 63`) steps, with any number of threads, no thread of any machine is stuck and none has a
top-level panic (`Robust`, `Robustness/Statement.lean`). Since the orchestrator panics unless
porcupine accepts the history, this says porcupine accepts every history, under every fault the
net extension allows. Proved in `Dsverify/Proof/.../paxosnet/TopLevelRobustness.lean`.''',
        addrs='paxosKitAddrs', steps='remoteStepBound',
        premises=[],  # none: the statement rests on Lean's three axioms
    ),
    # the deployment's address lists, in a module importing no kit spec (the statement's definitions
    # then say only what runs where; the definitions' names, namespaces and bodies as they were in
    # Deploy.lean and Kit.lean)
    addrs_module=dict(
        doc='''The paxos kit's addresses: the paxos nodes' (`PaxosAddrs()`) and the client machines'
(`ClientAddrs()`), the lists the statement's `paxosKitAddrs` joins (`TopLevelDefs.lean`); the protocol's
definitions (`Deploy.lean`) and the kit's specs (`Kit.lean`) import them.''',
        defs=[(PAXOS, '''/-- The deployment's node addresses (`paxosnet.PaxosAddrs()`): acceptors 1..3, learners 2001,
2002, then client `c`'s, `c = 0..3`. -/
def addrs : List GoString :=
  [go!"127.0.0.1:7401", go!"127.0.0.1:7402", go!"127.0.0.1:7403", go!"127.0.0.1:7404",
   go!"127.0.0.1:7405", go!"127.0.0.1:7406", go!"127.0.0.1:7407", go!"127.0.0.1:7408",
   go!"127.0.0.1:7409"]'''),
              (f'{PAXOS}.examples.paxosnet', '''/-- The client machines' addresses (`ClientAddrs()`), for the driver's calls. -/
def clientAddrs : List GoString :=
  [go!"127.0.0.1:7411", go!"127.0.0.1:7412", go!"127.0.0.1:7413", go!"127.0.0.1:7414"]''')],
    ),
    # what a challenge (kitgen --export-challenge) gives of the kit's Lean: the statement, its
    # definitions, the addresses, the package facts and gen-init's generated files; never the kit's
    # specs (`Kit.lean`: the client spec), the protocol's specs, invariants or proofs
    challenge_allow=['Dsverify.Spec.{pkg}.TopLevelRobustness', 'Dsverify.Proof.{pkg}.TopLevelDefs',
                     'Dsverify.Proof.{pkg}.Addrs', f'Dsverify.Proof.{PAXOS}.Base', f'Dsverify.Proof.{PAXOS}.Init',
                     'Dsverify.Proof.{pkg}.Base', 'Dsverify.Proof.{pkg}.Init',
                     'Dsverify.Proof.{pkg}.cmd.*.Base', 'Dsverify.Proof.{pkg}.cmd.*.Init',
                     'Dsverify.Proof.{pkg}.cmd.*.PkgTable'],
    defs=dict(
        doc='''The paxos kit's deployment (notes/dsv-paxos.md): its ten machines' boot programs and addresses, the
definitions its top-level statement (`Spec/.../paxosnet/TopLevelRobustness.lean`) names.''',
        imports=[f'public import Dsverify.Proof.{PAXOS}.examples.paxosnet.Addrs',
                 'public import Net.Statement.DistDeploy', 'public import Robustness.Statement'],
        system_doc='''The system: the ten machines, from the local states `σ i`: the orchestrator, client machines
0..3, servers 1..5 (each a command of `examples/paxosnet/cmd`).''',
        addrs_def='''/-- The deployment's addresses: the paxos nodes' (`PaxosAddrs()`) and the client machines'
(`ClientAddrs()`). -/
def paxosKitAddrs : List GoString := github_com.xiang90.paxos.addrs ++ clientAddrs''',
    ),
    proof=dict(
        doc='''The paxos kit's top-level result (`Spec/.../paxosnet/TopLevelRobustness.lean`), proved: from the
deployment's start (the protocol library's registry and the addresses unset), the ghost state
(`paxos_alloc`, the slot map, the pending library over the paxos register), the addresses'
protocols (the paxos nodes' the transport's, the client machines' remote's), and each machine's
boot program from its share, through `robust_of_distProtoRB`.''',
        imports=[f'public import Dsverify.Proof.{PAXOS}.examples.paxosnet.Linked',
                 'public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared',
                 'public import Net.Statement.DistBridge'],
        opens=['open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.xiang90.paxos',
               'open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)'],
        boot='plain',
        # the start: paxos's ghost state, remote's slot map with K = 3 call units per client
        # address, the addresses' protocols, the pending library; the shares' pieces
        start='''  iintro #Hreg Hs
  unfold paxosKitAddrs
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hsp, Hsc⟩
  imod mapCtx_alloc (Gg := G) (I := BStr) ⊤ clientAddrs 3 (by decide) with ⟨%ρ, -, #Hmap, Hbud⟩
  imod paxos_alloc (GF := remoteGF) ⊤ with ⟨%Γ, #Hpx, Hown, Hsts, Htoks⟩
  imod addrs_set_proto (Gg := G) ⊤ (fun _ => wireProto (msgOK Γ)) (fun _ => noProto) addrs
    $$ Hreg Hsp with #Hpp
  imod addrs_set_proto (Gg := G) ⊤ (fun a => reqP (Gg := G) (RBase.svc (woR Γ)) a)
    (fun _ => repP (Gg := G) (RBase.svc (woR Γ))) clientAddrs $$ Hreg Hsc with #Hpc
  have hv : own_state (G := G) Γ none ⊢ (woR (Gg := G) Γ).sysState (woR (Gg := G) Γ).B.init := .rfl
  ihave Hown := hv $$ Hown
  imod pend_alloc (Gg := G) (woR Γ) ⊤ (woS0 (GF := remoteGF)) rfl $$ Hown with ⟨%γp, #Hpend, Hlib⟩
  ihave #Hprotos : allProtos (G := G) Γ $$ [Hpp]
  · unfold allProtos; iexact Hpp
  ihave #Hra : [∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (woR Γ) a $$ [Hpc]
  · unfold remoteAddr svcAddr; iexact Hpc
  unfold accIds
  icases BigSepL.bigSepL_cons.1 $$ Hsts with ⟨Hst1, Hsts⟩
  icases BigSepL.bigSepL_cons.1 $$ Hsts with ⟨Hst2, Hsts⟩
  icases BigSepL.bigSepL_cons.1 $$ Hsts with ⟨Hst3, -⟩
  icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Htok0, Htoks⟩
  icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Htok1, Htoks⟩
  icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Htok2, Htoks⟩
  icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Htok3, -⟩
  ihave #Hra0 : remoteAddr (Gg := G) (woR Γ) (clientAddrs.getD 0 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 0) rfl $$ Hra
  ihave #Hra1 : remoteAddr (Gg := G) (woR Γ) (clientAddrs.getD 1 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 1) rfl $$ Hra
  ihave #Hra2 : remoteAddr (Gg := G) (woR Γ) (clientAddrs.getD 2 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 2) rfl $$ Hra
  ihave #Hra3 : remoteAddr (Gg := G) (woR Γ) (clientAddrs.getD 3 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 3) rfl $$ Hra''',
    ),
    mains=dict(
        doc='''The paxos kit's ten commands' `main`s (`examples/paxosnet/cmd/*`), each its kit function on its
constants, from the kit functions' specs (`Kit.lean`).''',
        imports=[f'public import Dsverify.Proof.{PAXOS}.examples.paxosnet.Kit'],
        opens=['open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net',
               'open github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.xiang90.paxos',
               '  github_com.xiang90.paxos.examples.paxosnet'],
        variables=_MAINS_VARS,
    ),
)
