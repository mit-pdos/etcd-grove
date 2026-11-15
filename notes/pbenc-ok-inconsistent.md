---
title: pbEnc_ok is inconsistent: a caller-built PbType proves False
found: 2026-11-07
by: axiom sweep B1-1 (etcd-grove-c9), notes/axiom-sweep-plan.md on branch axiom-sweep
blocks-proof: yes
status: fixed by per-type stage A (lean de9c19e020, 2026-11-10): pbEnc_ok deleted; encodings keyed on wire content of registered types (entryEncC_ok, msgEncC_ok, *_reg)
---
# `pbEnc_ok` is inconsistent: a caller-built `PbType` proves `False`

This is a bug in this repository's trust base, not in etcd. It is recorded here and not in
`nonissues/`, in a non-issue's shape.

The trust-boundary axiom `pbEnc_ok` (`Proof/google_golang_org/protobuf/proto/InvProto.lean:81`) is
quantified over any `T : PbType GF`. `PbType` is a record whose fields *are* the trusted model of a
protobuf message type: `ro`, `marshals`, `wire`, `eqv`, `blank` and `dec`. The axiom's only premise
is the record's own `T.ro l m`. Anyone can build such a record:

- **One bad record.** Take `ro := True`, `marshals := True` and `wire := False`. Then `pbEnc_ok`
  gives `⌜False⌝` from `True`, and Iris's pure soundness turns that into Lean's `False`.
- **Two records that disagree.** `pbEnc` depends only on `(T.ty, l)`. Two records of the same Go
  type whose `wire` models disagree, say on whether `[]` encodes the message, make the axiom assert
  both.

The axiom needs no instance but `GF`. At `Iris.BundledGFunctors.default` the result is a **closed
`False`, with no hypothesis**.

**Why not an issue:** a bug in our trust base. Go's `proto.Marshal` is fine; the axiom states its
model at a quantifier that no Go fact supports.

## Proof

yes (until 2026-11-10): every result whose `#print axioms` listed `pbEnc_ok` was vacuous until the fix landed. Fixed: no result lists it any more (etc/tcb-baseline.txt).

**The derivation.** Branch `axiom/pbenc-inconsistent`, commit `f238daef0c` (not on `lean`), file
`Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/pbenc/False.lean`:

```lean
def badPb (ty : go.GoType) : PbType GF where
  ty := ty; M := Unit; ro := fun _ _ => iprop(True); ro_persistent := fun _ _ => inferInstance
  marshals := fun _ => True; wire := fun _ _ => False
  eqv := fun _ _ => True; blank := fun _ => iprop(True); dec := fun _ _ => iprop(True)

theorem pbEnc_ok_closed_false : False := by
  have h := pbEnc_ok (badPb (GF := Iris.BundledGFunctors.default) (default : go.GoType))
    (default : Loc) ()
  refine (pure_soundness (PROP := IProp Iris.BundledGFunctors.default) (φ := False) ?_)
  refine h.trans ?_
  apply pure_mono
  intro ⟨hw, _⟩
  exact hw trivial
```

The file has two more theorems:

- `pbEnc_ok_false (ty) : False`, for any `GF` and any Go type;
- `pbEnc_ok_disagree (ty) : False`, from the two disagreeing records.

`#print axioms` of each of the three: `[propext, Classical.choice, Quot.sound,
Perennial.EtcdGrove.pbEnc_ok]`.

**What rests on it.** This is from `.lake/tcb.json` at `lean` `158829a8b9` (the build of
`etc/tcb-report.py --per-root`):

- 83 of the 4898 linked results list `pbEnc_ok`;
- 40 of the 881 exported results list it.

Of those 40, 17 are `*_safe` results:

- `etcd_cache_safe`, `etcd_compacted_safe`, `etcd_compactwatch_safe`;
- `etcd_lease_safe`, `etcd_leasecatchup_safe`, `etcd_leaseexpiry_safe`, `etcd_leasegrant_safe`;
- `etcd_partition_safe`, `etcd_partition_watch_safe`;
- `etcd_putget_safe`, `etcd_putget3_safe`;
- `etcd_txnlin_safe`, `etcd_watch_safe`;
- `k8s_compactor_safe`, `k8s_compactor_partition_safe`;
- `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe`.

The other 23 are:

- the examples' `Main` triples:
  - `authkv_Main`, `cachekv_Main`, `putgetc_Main`, `compactkv_Main`;
  - `leasekv_Main`, `leasecatchup_Main`, `leaseexpiry_Main`, `leasegrant_Main`;
  - `linkv3p_Main`, `linkv3p_MainWatch`;
  - `putget_Main`, `putget3_Main`, `linkvtxn_Main`, `watchkv_Main`;
  - `k8s_compactor_Main`, `k8s_compactor_MainPartition`;
  - `k8setcd3_Main`, `k8setcd3_MainCluster`;
- the server's results: `etcdstart.wp_BuildServer`, `applyAll_model`, `server_apply_all_snap_m`,
  `server_run` and `start_gives_views`.

So every closed result through the server is affected. Results whose `#print axioms` does not list
`pbEnc_ok` are unaffected: raft's results, the cache's own, the B-tree's, bbolt's, porcupine's.
Those may still list the `proto.*Pb` specs below; see "Notes".

## Notes

**The other `PbType` specs have the same shape.** They are `proto.{Marshal,Size,Unmarshal,Clone,
MarshalAppend}Pb` (`Spec/google_golang_org/protobuf/proto/*Pb.lean`). Each reaches the same 40/17 results, and they are refuted as well (2026-11-07, branch `axiom/pbtype-specs`, `0f1f10d1d1`, `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/pbtype/False.lean`): with a record whose `wire` and `eqv` are false, `Marshal`/`Size`/`Clone`/`MarshalAppend` of a `*T` get `WP … {{ Φ }}` for every `Φ`; with `wire` true, `Unmarshal(b, nil)` returns `nil` for any bytes, so `if proto.Unmarshal([]byte{0xff}, &Entry{}) != nil { panic }` is proved safe. A contradiction with Go, not a closed `False` (that needs an adequacy theorem); `#print axioms` of each: Lean's three plus that one spec. They join the fix. grpc's `ProtoMsg` axioms and the other record-quantified ones are being checked (part (3) of the decision below); a confirmed one joins it too.

The repository has two genuine instances, `pbMessage` and `pbEntry`
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/PbMessage.lean:78,116`).

**The fix, as the user decided via etcd-grove-82 on 2026-11-07.** Per-type axioms, as their own
stage, ahead of the rest of the sweep. Its Scope goes to etcd-grove-82 before any Lean is written:

- state `pbEnc_ok` and the `*Pb` specs only at the concrete trusted instances;
- make each wire model a fixed definition, with a satisfiability lemma: every message that marshals
  has some bytes that encode it;
- add a fail-closed gate that refuses an axiom quantified over a user-buildable model record;
- attack the restated axioms before the Freeze.

The review report is `notes/axiom-review/pbenc.md`.
