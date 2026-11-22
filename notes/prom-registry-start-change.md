# `goose_adequacy_start` without the metric names (for Upamanyu's sign-off; branch `prom-registry`)

`Proof/runtime/Start.lean`'s `goose_adequacy_start` is the trusted start model. Branch `prom-registry`
(mit-pdos/etcd-grove#15, notes/prom-registry.md) removes its prometheus part. **Nothing is added**:
the change only deletes premises and a conjunct of the rights. Not landed; waiting for sign-off.

## Why

The rights to register metric names (`prometheus.nameFree n`) were opaque axiomatized resources that
only this axiom handed out, once per run, under the premise `namesUnclaimed e Ns` (no unverified code
registers those names) and `descIdsDistinct Ns`. In a crash program (the WAL tester restarts after each
crash and re-registers its metrics) a `nameFree` unused in one run could be carried through the crash
frame and held twice in the next: the rights must belong to a run, which an axiom over executions
cannot say. On the branch the default registry is a model on the Go heap (`examples/lib/promreg`, Go,
translated and verified, with a trusted glue for `Register`/`MustRegister`/the initializer, evidence
`examples/lib/promreg/model_test.go` against client_golang v1.24.1); `nameFree n` is an element of a
ghost map that each run's proof allocates itself (`promReg_alloc`, an ordinary ghost allocation), and
the registry's invariant, built by that run's prometheus initializer on that run's heap, owns the
element of every registered ID. So the rights come from the logic, the crash adequacy's fresh heap and
fresh ghost allocation reset them, and the start model needs to hand out nothing for prometheus. What
`namesUnclaimed` also said, that unverified code registers nothing extra, is now a claim of the
specific untranslated code that could register (its specs; notes/prom-registry.md §5 lists it: no
untranslated code in any verified closure registers with the default registry, and grpc-prometheus's
server metrics are registered by translated code whose `Register.spec` takes their rights).

## Old statement (verbatim, `lean` 753af63859)

```lean
def startRights {GF : BundledGFunctors} [GooseExts] (Ns As Ds : List GoString) : IProp GF :=
  iprop(([∗list] n ∈ Ns, prometheus.nameFree n) ∗ ([∗list] a ∈ As, netAddrFree a) ∗
    ([∗list] a ∈ As, httpProtoFree a) ∗ ([∗list] d ∈ Ds, dataDirFresh d) ∗
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    envVerifyOff)

axiom goose_adequacy_start [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Ns As Ds : List GoString) (hNs : Ns.Nodup) (hAs : As.Nodup) (hDs : Ds.Nodup)
    (hAsLit : ∀ a ∈ As, netAddrLit a = true)
    (hNsFree : prometheus.namesUnclaimed e Ns) (hAsFree : addrsUnclaimed e As)
    (hDsFree : dataDirsAbsent e Ds) (hEnv : verifyEnvOff e)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok -∗ startRights (GF := GF) Ns As Ds ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow T n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)
```

`goose_adequacy_start_all` (a theorem from it) also has `(hNsIds : prometheus.descIdsDistinct Ns := by
decide +kernel)`, and `prometheus.nameUnclaimed` (an axiom) and `prometheus.namesUnclaimed` (its
definition) are declared in the same file.

## New statement

```lean
def startRights {GF : BundledGFunctors} [GooseExts] (As Ds : List GoString) : IProp GF :=
  iprop(([∗list] a ∈ As, netAddrFree a) ∗
    ([∗list] a ∈ As, httpProtoFree a) ∗ ([∗list] d ∈ Ds, dataDirFresh d) ∗
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    envVerifyOff)

axiom goose_adequacy_start [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (As Ds : List GoString) (hAs : As.Nodup) (hDs : Ds.Nodup)
    (hAsLit : ∀ a ∈ As, netAddrLit a = true)
    (hAsFree : addrsUnclaimed e As)
    (hDsFree : dataDirsAbsent e Ds) (hEnv : verifyEnvOff e)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok -∗ startRights (GF := GF) As Ds ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow T n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)
```

`goose_adequacy_start_all` loses `Ns`, `hNs`, `hNsFree` and `hNsIds` the same way;
`prometheus.nameUnclaimed` (axiom) and `prometheus.namesUnclaimed` are deleted. The header's
paragraphs on names (and the satisfiability argument's `nameFree` reading) go.

## Closed theorems whose premises shrink

Each loses exactly its `HNs : prometheus.namesUnclaimed (…) Names` premise (and, where present, the
implicit `Ns`, `hNs : Ns.Nodup` and `hNsIds`); nothing else in any statement changes:

- `etcd_robust.spec` (`Spec/.../examples/etcd/all/TopLevelRobustness.lean`) and `etcd_safe`
  (`Proof/.../examples/etcd/all/Results.lean`);
- `etcd_leaseexpiryN_robust.spec` and `etcd_leaseexpiryN_safe` (`examples/etcd/leaseexpiryN`);
- `k8s_robust.spec` and `k8s_safe` (`examples/k8s/all`);
- `mvccfull_robust.spec`, `mvccfull_safe`, `mvccfull_adequate` (`examples/mvccfull`);
- `mvccrand_robust.spec`, `mvccrand_adequate` (`examples/mvccrand`);
- the generic start theorems they go through: `etcdstart`'s `init_adequate(_below)`,
  `etcd_adequate(_below)`, `etcd_adequate_alloc(_below)` (`Adequacy.lean`) and
  `etcd_adequate_members(_below)`, `etcd_adequate_alloc_members(_below)` (`AdequacyMembers.lean`).

(The list is from the branch's base; the final diff will be checked against it when the threading
stage is done.)
