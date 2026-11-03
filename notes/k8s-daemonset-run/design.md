# The run's cross-track contracts (Stage 3)

What one track's statements promise another. A change to anything here after it is agreed is a
thaw: say so in the track's report, with the reason.

## Who owns the API state

`apimodel.apiState γa σ` (the clients' half of the model server's history; every typed client
operation is logically atomic over it) is owned by **S1's invariant** (`dsctl.s1Inv`, track B),
allocated by `Main` (track C) right after `apimodel.NewServer`. Every client operation therefore
linearizes inside `s1Inv`:

- the informers' list and watch (track A) only read: they need **read access** to the API state,
  not `s1Inv` itself. Track A defines a persistent predicate for it, in the API model's vocabulary
  (a new module under `Proof/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/`, owned
  by A), shaped like: from it, a read's atomic update can be fired at the current `σ` and given back
  unchanged (for instance `□ |={⊤, ⊤ ∖ N}=> ∃ σ, apiState γa σ ∗ (apiState γa σ ={⊤ ∖ N, ⊤}=∗ True)`
  for a namespace `N` the predicate names). The typed informers' list-watch closures (gap D2's
  `NewTyped*InformerWithOptions`) produce `lwOk` (`RefInf.lean`) from it and the clientset. Track C
  proves it from `s1Inv` (a read leaves `σ`, so `s1Ok`, unchanged).
- the controller's writes (pod creates and deletes, status updates, revision creates) fire their
  atomic updates inside `s1Inv` (track B), keeping `s1Ok`.
- the checker's list (`dsmain.check`, track C) fires its read inside `s1Inv` and gets S1 at the
  listed state.

## The informer as the controller sees it

`dsctl.infAt γa r I Fam` (`daemon/Defs.lean`): the store (`isCache` over `infObj`) and the
informer invariant `infInv`. Track A's lifecycle specs (the typed informer's `Informer()`,
`GetStore`, `GetIndexer`, `Lister`) give exactly this, or a law from what they give to it.

## The handler contract (A defines, C uses)

`AddEventHandlerWithOptions(h, opts)` takes a contract on the handler's three functions. What the
DaemonSet controller's handlers need from it (and nothing more, by the spec principles):

1. **Types.** `OnAdd(x)`, `OnUpdate(old, cur)`: `x`, `old`, `cur` registered objects of the
   informer's resource (`infObj`: so `obj.(*v1.Pod)` does not panic). `OnDelete(x)`: a registered
   object, or a `cache.DeletedFinalStateUnknown` whose `Obj` is one.
2. **What a delete means.** For S1: the DaemonSet handler `deleteDaemonset` calls
   `consistencyStore.Clear(owner, uid)`, which forgets the owner's recorded writes; S1's accounting
   survives only if that happens when the DaemonSet with that UID is gone. So `OnDelete`'s object
   (or tombstone's) must be absent from the API state from some version on: e.g. "there is a past
   state `σp` and a version `v` with the object's key absent from `tableAt (σp.tbl r).log v`, and
   the object's own version at most `v`". Similarly `OnUpdate(old, cur)`: both objects of one key,
   `old`'s version at most `cur`'s, both entries of the log at their versions (so the UID differs
   only after a delete). Track A states the strongest such facts the informer contract gives.
3. **Resources.** A handler runs on the processor's listener goroutine: the contract lets the
   handler take, per listener, a resource the registering code gives (the controller's handlers
   need one reader slot of each store they read, of the expectations' store, and the work queues'
   `Add`; a persistent `isDsc`).

## The controller object

`dsctl.isDsc dsc c γ cfg podFam dsFam crFam nodeFam` (`daemon/Defs.lean`, track B owns it): track B
fixes its final shape first (it is what `NewDaemonSetsController` gives and every method takes);
track C proves `NewDaemonSetsController` produces it.

## S1's invariant (B)

**Thaw (track B, 2026-11-03):** two invariants, not one. The consistency store allocates its own
ghost names inside `NewDaemonSetsController`, so no invariant holding `consState` can exist right
after `NewServer`. `apiInv γa γ` (allocated by `Main` right after `NewServer`) holds `apiState`
and half of a mirror of it (`ghostVar γ.mirror`); `apiReader` follows by `apiReader_of_inv`.
`s1Inv γ c` (allocated by `Main` after the constructor, before `Run` and the admin's DaemonSet
create) holds the mirror's other half, the consistency store's state, the per-owner bookkeeping and
the claims, with `s1Ok`: S1 for every UID, `sceneOk` (what the model and the controller keep true of
every object), per-owner accounting. Track B's report has the full text (`S1Inv.lean`).

The text below is the first version:

`s1Inv` holds the API state's clients' half, the consistency store's abstract state, the pod
informer's version lower bound, the pending creates and claimed nodes (`S1Inv.lean`). Track B
decides whether it covers one DaemonSet (the driver's: its key `default/ds-1`, its UID fixed when
the admin's create commits) or every DaemonSet (per owner bookkeeping), by the spec principles
(one general spec; the invariant is the client's, `Main`'s, but the sync's spec must not be
specialized to the driver's constants). Facts S1 needs about the scenario that the model's API
gives: a DaemonSet is never deleted (the model's DaemonSet client has no `Delete`), its spec never
changes (`UpdateStatus` changes only the status: `dsStatusMut`), so no surge (`MaxSurge 0` after
the model's defaults) and the rolling update never creates pods.

## The ambiguous create

`syncNodes`' create goroutine, on an error after a committed create (`createErrOutcome`'s
`.ok (true, _)` branch with `AmbiguousWrites`): S1's accounting has no step (the pod is pending
with no version to record). The proof leaves exactly that branch `sorry`, with a comment naming
`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md` and `ambiguous_create_breaks_S1`. No
other `sorry` may be justified by it.
