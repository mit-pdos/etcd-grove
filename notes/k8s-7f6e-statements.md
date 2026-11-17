# k8s 7f-6 stage E, checkpoint E-2: the closed statements, old → new (2026-11-17)

For the coordinator (etcd-grove-03) and the user. Nothing is linked yet: `Link`, `MainLinked`,
`Adequacy`, `Results` and the interfaces are unchanged on `k8s-7f6` (step 10, after approval). The
Main* specs below are committed (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/Main*.lean`)
and proved (`Proof/.../Main*.lean`, built). The theorems' texts are the planned ones (Scope §2's
sketch): only the changes are listed; everything else stays word for word.

## 1. The Main* specs (`Main.spec`, `MainCluster.spec`, `MainPartition.spec`)

Same change in all three (committed, 771b092979):

| old | new |
| --- | --- |
| (binders) | `+ [EtcdGrove.ContextReadErrs] [ContextErrsClient]` (instance binders of the `∀`, as `k8s_compactor`'s Main.spec) |
| `(clients ops : w64)` | `(clients ops watchers wops : w64)` |
| `0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →` | `0 ≤ sint.Z clients → 0 ≤ sint.Z watchers → sint.Z clients + sint.Z watchers < 2 ^ 31 → 0 ≤ sint.Z ops → 0 ≤ sint.Z wops →` |
| `sint.Z clients * sint.Z ops < 2 ^ 60 →` | `sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60 →` |
| `Main #clients #ops` (`MainCluster #k #clients #ops`, `MainPartition #k #clients #ops #sched`) | `Main #clients #ops #watchers #wops` (`MainCluster #k #clients #ops #watchers #wops`, `MainPartition #k #clients #ops #watchers #wops #sched`) |

Pre and post unchanged (`⌜r = "Ok" ∨ r = "Unknown"⌝`). The docstrings name `Check(s, st0, h0, clients,
ops, watchers, wops, 0)`.

## 2. The spec results (`Results.lean`: `k8setcd3_Main`, `k8setcd3_MainCluster`, `k8setcd3_MainPartition`)

Text unchanged (`… : k8s_etcd3.Main.spec := k8s_etcd3.wp_Main`, and the two others); their meaning
moves with §1. The `[ContextReadErrs]` binder they already have stays; `ContextErrsClient` is a binder
of the spec itself (§1), so the results need none.

## 3. The three theorems (`k8s_etcd3_safe`, `k8s_etcd3_cluster_safe`, `k8s_etcd3_partition_safe`) and their `_adequate`

Same changes in the six (`Results.lean` and `Adequacy.lean`):

| old | new |
| --- | --- |
| `(Hctx : ∀ hG, ContextReadErrs …)` | unchanged, followed by `(Hcec : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextErrsClient (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))` (Q4, approved by the user 2026-11-16) |
| `(clients ops : w64)` | `(clients ops watchers wops : w64)` |
| `(Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)` | `(Hc0 : 0 ≤ sint.Z clients) (Hw0 : 0 ≤ sint.Z watchers) (Hc31 : sint.Z clients + sint.Z watchers < 2 ^ 31) (Hops : 0 ≤ sint.Z ops) (Hwops : 0 ≤ sint.Z wops)` |
| `(Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)` | `(Hmul : sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60)` |
| `k8setcd3Program clients ops` | `k8setcd3Program clients ops watchers wops` (in `HNs`, `HAs`, `HDs`, `HEnv`, `Hsteps`) |
| `k8setcd3CProgram k clients ops` | `k8setcd3CProgram k clients ops watchers wops` |
| `k8setcd3PProgram k clients ops steps` | `k8setcd3PProgram k clients ops watchers wops steps` |

`k8setcd3Program`/`CProgram`/`PProgram` (`Adequacy.lean`, the programs `Main(…)`/`MainCluster(…)`/
`MainPartition(…)` applied to their arguments) gain the two arguments. The conclusion (returns `Ok`
or `Unknown`, not stuck, no panic) is unchanged. No other premise: the members, addresses, data
directories, `premises`, `Hn` are as today.

## 4. `MainLinked.lean`

`wp_MainCluster`/`wp_MainPartition` (and `Link.lean`'s `wp_Main`) link the new proofs:
`MainCluster.wp_proof wp_NewNop wp_startCluster wp_newStore context.wp_ErrAny wp_Check` (and the
Partitioner for `MainPartition`); `Main.wp_proof … wp_newStore context.wp_ErrAny wp_Check hne Hp Hr`
and `startCluster.wp_proof … Hp Hr`, the two mvcc laws (`persistent`, `mvccState_reachable`)
discharged by their `_law_holds` as the compactor's `MainLinked` does (E-1 decision 2). The new
specs (`newStore`, `WContract`'s callees `runtime.Decode`, `codec.Decode`,
`storage.AnnotateInitialEventsEndBookmark`, `Obj.GetAnnotations`, `Obj.SetAnnotations`, `meta.Accessor`)
are linked in `etc/link-lean-first-k8setcd3.txt`/`-k8s-etcd3.txt`. No axiom, no `sorry`, no trusted
text added by E (expected `tcb-report --check` diff: none from E; 7f-5's items already on lean).

## 5. Forms decided since E-1 (questions.md, "Stage E (seventh agent)")

- `storage.AnnotateInitialEventsEndBookmark.spec` (new, generic): any `metav1.Object` whose
  `GetAnnotations`/`SetAnnotations` meet the caller's contract (`P`, `R`, `Q`); post `err = nil ∗ Q`.
- `Obj.GetAnnotations.spec`/`Obj.SetAnnotations.spec` (new, driver): the annotation map exactly.
- `newObj.spec`'s post `⌜x ≠ nil⌝` → `objAtD x dzero []` (stronger post).
- `WContract.lean`: `watchContractOk_driver`, `newItemOk_driver`, the vocabulary `storeCfgD`.
- `WatchEnvN.lean`: `clientWatchOk_of_regs` (+ `memberWatch_of_reg`, `streams_of_regs`, `regs_lookup`,
  `wmemsOf_*`); the watch condition via `etcdstart.srvOnce_of_plan` inline (the compactor's
  `srvOnce_of_one` not imported).
- `newStore.spec` (new, plan step 8): post the seed cell at `σs2`, the seeded store, `rangeStreamOff`,
  `watchListOn`, `isStore sp (storeCfgD …)`, `□ ∀ γk, clientWatchOk cl γk -∗ storeWatchOk sp (storeCfgD …) driverW γk`.
- `Main`'s client watch environment: `watchEnvL m0 (wmemsOf [x] [(srv, R)]) ρ.rd wpfx` in place of
  `srvWEnv R … default` (the one member as the `k`-member path has it).
- `Main.wp_proof` takes the two mvcc laws `Hp Hr` (as `startCluster.wp_proof`; E-1 decision 2).
