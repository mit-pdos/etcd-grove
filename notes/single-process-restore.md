# Restoring the single-process theorems over the net extension (2026-11-23, etcd-grove#28)

The net swap (etcd-dist D2's `net` half, `82847d941b`, landing `640fd426f3`; `notes/etcd-dist-plan.md` §9)
made the main tree's `net` the part `Net/`'s, over the net extension, and retired three single-process closed
theorems with it: `etcd_safe`/`etcd_robust` (`examples/etcd/all`), `k8s_safe`/`k8s_robust`
(`examples/k8s/all`) and `etcd_leaseexpiryN_safe`/`_robust` (`examples/etcd/leaseexpiryN`). Their last
proved form is tag `single-process-final` (`d9d1f32018`). This branch (`single-process-restore`) brings them
back under the names `etcd_safe_single_process`, `k8s_safe_single_process`,
`etcd_leaseexpiryN_safe_single_process` (and `*_robust_single_process`): the distributed theorem has the plain
names (Upamanyu, #24).

The route: **no new axiom**. The per-function proofs (`Main`, `MainLinked`, the drivers) were kept by the
swap and are unchanged; the programs run over `etcdNetExts := [idIssueExt, fsExt, netExt]`
(`examples/lib/etcdstart/NetExts.lean`); the right to listen at an address (`netAddrFree`, a definition since
the swap: `addrClaim a ∗ netLisTok a ∗ ⌜addrOk a⌝`) is assembled at adequacy from program start's
`addrClaim a` and the net extension's listening token `netLisTok a` (its start resources); and program
start's address part, removed at the swap, is restored minimally: it hands out the two axiomatized rights
nothing else produces, `addrClaim` and `httpProtoFree`, and nothing the extension hands out.

## The start axiom: before and after

**At `single-process-final`** (before the swap; `netAddrFree` an axiomatized predicate):

```lean
def startRights {GF : BundledGFunctors} [GooseExts] (Ns As Ds : List GoString) : IProp GF :=
  iprop(([∗list] n ∈ Ns, prometheus.nameFree n) ∗ ([∗list] a ∈ As, netAddrFree a) ∗
    ([∗list] a ∈ As, httpProtoFree a) ∗ ([∗list] d ∈ Ds, dataDirFresh d) ∗
    envVerifyOff)

axiom goose_adequacy_start [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Ns As Ds : List GoString) (hNs : Ns.Nodup) (hAs : As.Nodup) (hDs : Ds.Nodup)
    (hAsLit : ∀ a ∈ As, netAddrLit a = true)
    (hNsFree : prometheus.namesUnclaimed e Ns) (hAsFree : addrsUnclaimed e As)
    (hDsFree : dataDirsAbsent e Ds) (hEnv : verifyEnvOff e)
    (Hwp : ∀ [hG : HeapGS .hasLC GF], receiptBound GF = N → threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗ extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok -∗ startRights (GF := GF) Ns As Ds ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow T n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)
```

with `axiom addrUnclaimed [GooseExts] (e : Expr) (a : GoString) : Prop` and
`def addrsUnclaimed e As := ∀ a ∈ As, addrUnclaimed e a`.

**After the swap (`82847d941b`)**: `startRights Ns Ds` (no addresses), `goose_adequacy_start` without `As`,
`hAs`, `hAsLit`, `hAsFree`; `addrUnclaimed`/`addrsUnclaimed` deleted.

**This branch**: the axiom's statement is again the one above, word for word (`As`, `hAs`, `hAsLit`,
`hAsFree : addrsUnclaimed e As`; `addrUnclaimed` and `addrsUnclaimed` restored with their text, part (a)
annotated), and `startRights` hands out `addrClaim` where it handed out `netAddrFree`:

```lean
def startRights {GF : BundledGFunctors} [GooseExts] (Ns As Ds : List GoString) : IProp GF :=
  iprop(([∗list] n ∈ Ns, prometheus.nameFree n) ∗ ([∗list] a ∈ As, addrClaim a) ∗
    ([∗list] a ∈ As, httpProtoFree a) ∗ ([∗list] d ∈ Ds, dataDirFresh d) ∗
    envVerifyOff)
```

`goose_adequacy_start_all` (the theorem with `goose_adequacy`'s thread premise) follows the same signature.
The two other callers, `mvccfull`'s and `mvccrand`'s adequacy, pass `As = []` (as at the tag).

## Why each piece is needed

- **`addrClaim a`** (axiomatized since the swap, `Proof/net/InvNet.lean`): the first conjunct of
  `netAddrFree a`, which every listener's spec takes (`net.Listen.spec`, through `memberStartRes`, the members'
  start bundles, and the bridges' addresses). It is the closed-world claim on `a`'s requests that the grpc and
  net/http transport axioms rest on (`grpc.start`, `http.register`) until phase 7 (S2, S5) proves the
  transport over the net extension. Nothing in the logic produces it: without program start it cannot be had,
  and no single-process program could listen.
- **`httpProtoFree a`** (axiomatized, `InvNet.lean`): the right to fix `a`'s HTTP protocol (`http.reserve`), which
  a raft member's peer address needs before its listener exists (D39a). Purely ghost; nothing else produces it.
- **`As`, `hAs`, `hAsLit`, `hAsFree`**: the rights are per address and exclusive, so the addresses are distinct
  (`hAs`); per-string rights are per-socket and never proxied only for numeric loopback literals (`hAsLit`,
  `netAddrLit`: the names-only `http.Transport` still reads `ProxyFromEnvironment` until S5); and the program
  start may hand out the claim only for addresses the program owns (`hAsFree`).
- **Not handed out: `netLisTok a`**, the right to listen at `a` in the net extension. It is the extension's, in
  its global start resources (`Net.netStart`: one token per valid address), which `goose_adequacy_start`'s WP
  proof already receives (`extsGlobalStart`). The adequacy wrapper takes it from there
  (`netAddrFrees_start`, `NetExts.lean`), for addresses valid for the extension (`Net.addrOk`, proved of each
  program's addresses: every port is below 32768, `addrOk_loopback`).

## Why it is sound

The axiom is the tag's axiom with `netAddrFree a` narrowed to `addrClaim a`: it hands out strictly less (the
tag's `netAddrFree` is now `addrClaim ∗ netLisTok ∗ ⌜addrOk⌝`), under the same premises. The satisfiability
argument of `Start.lean`'s header carries over: read `nameFree`, `addrClaim`, `httpProtoFree` as `True` (no axiom
says any is exclusive) and the axiom's premise is `goose_adequacy_below`'s and its conclusion its conclusion.

**The axiom and the extension hand out disjoint rights.** The start axiom gives `addrClaim` and
`httpProtoFree`, axiomatized predicates no definition or other axiom produces (checked: the only declarations
are `InvNet.lean`'s; the only producer is `startRights`). The net extension gives `netLisTok` (its ghost map
`γtok`, allocated by `net_global_init`, `GooseLang/Ext/Net/Ghost.lean`), never the axiom. So no right exists
twice: an address is listened on at most once because `netLisTok` is exclusive (`netLisTok_excl`) and
`addrClaim` too is consumed by `Listen` into `netListenerAt` (`grpcAddrIs_agree`'s "one server per address").
Before the swap the axiom handed out the whole listen right (`netAddrFree`); handing out `netLisTok` too would
have duplicated the extension's token, which is why the axiom's `startRights` names `addrClaim`, not
`netAddrFree`.

## What stays a premise

- **`addrsUnclaimed e As`** (`HAs` of each statement), both parts, as at the tag. (a), the world assumption: no
  other process binds or connects to an address of `As`. It is still needed over the net extension: the models'
  gRPC and HTTP traffic (grpc's `ClientConn`, rafthttp's `http.Transport`) does not go through the extension
  (`grpc.start`, `http.register` are trust-boundary axioms over `addrClaim`), so the extension's closed network
  says nothing of a foreign connection to a gRPC or HTTP listener. (b), what the program's own connections
  carry: what `addrClaim` stands for.
- **`net.FieldAssumptions`** (Net's hand-stated facts of `net`'s structs, as `os.file.FieldAssumptions`): an
  instance argument of each restored statement, since `net.Listen` is now proved from Net's spec (a semantic
  premise of every linked result reaching it since the swap).
- **The network's initial state**: no connection (`extsInitGlobal`, `Robust`'s own premise on the extensions'
  initial states, which the single-process `Robust.of_single_below` dropped: `robust_of_single_below_init`,
  `AdequacyMembers.lean`) and no listener (the process is fresh).

## What changed in the statements

Against `single-process-final`: the names (`*_single_process`); the bundle (`etcdNetExts` for `etcdFsExts` in
the `attribute [local instance]` line: the semantics gains the net extension, every fault it allows); the
instance argument `[net.FieldAssumptions]`; `etcd_safe_single_process` and its siblings take `extsInitGlobal g`
(the robustness statements had it already). No other premise.

## Files and who does what

The shared part (this note's first commit): `Proof/runtime/Start.lean` (the address part), `Proof/net/InvNet.lean`'s
header, `mvccfull`/`mvccrand`'s call sites (`As = []`), `examples/lib/etcdstart/NetExts.lean` (the bundle,
`etcdNetFs_start`, `netAddrFrees_start`, `addrOk_loopback`) and `examples/lib/etcdstart/AdequacyMembers.lean`
(`etcd_adequate_alloc_below`, `etcd_adequate_below`, `etcd_adequate_members_below`,
`etcd_adequate_alloc_members_below` over `etcdNetExts`, taking `hAsOk : ∀ a ∈ As, Net.addrOk a = true` and
`Hinitg`; `robust_of_single_below_init`).

Per theorem: the files restored from the tag under the same paths (`TopLevelRobustness` Spec and Proof,
`TopLevelDefs`, `Results`, `Adequacy`, `Disjoint`, `PkgTable` regenerated by `etc/gen-init.py`, its `PROGRAMS`), the
`attribute [local instance]` lines switched to `etcdNetExts … etcdNetExts_hasNet`, `goosePreGExts` given a third
entry, `[net.FieldAssumptions]` and `Hg : extsInitGlobal g` added, `Hinitg := ⟨trivial, trivial, Hg.2.2.1,
trivial⟩`, an `…Addrs_ok` lemma (from the drivers' `addr_port` and `addrOk_loopback`) passed as `hAsOk`, and a
collection `etc/tcb-collections/*-single-process.txt`. `etcd_safe_single_process`: this branch. `k8s_safe_single_process`
and `etcd_leaseexpiryN_safe_single_process`: zeldovich's session (coordinator, 2026-11-23); drafts of both were
started here and set aside.
