# `goose_adequacy_start`: rights of names whose descriptor IDs collide (prove-promdeep, 2026-11-20)

Found by reading client_golang v1.24.1 (`prometheus/desc.go`, `registry.go`) while triaging its
axioms for translation; confirmed by a Go test and in Lean.

## The claim

`EtcdGrove.goose_adequacy_start` (`Proof/runtime/Start.lean`) hands the program's WP proof
`prometheus.nameFree n` for each name of a duplicate-free list `Ns` of which `namesUnclaimed e Ns`
holds. `nameFree n` (`Proof/github_com/prometheus/client_golang/prometheus/Registry.lean`) is the
exclusive right to register `n`: no collector registered with the default registry, now or later
by anyone but the holder, has a descriptor named `n`, **or whose ID (or collector ID) is the ID of
`n`'s label-free descriptor**. `prometheus.MustRegister.wp_proof` relies on that last clause:
`Registry.Register` (`registry.go:283-376`) refuses a collector whose descriptor ID is already in
`descIDs` or whose collector ID (the XOR of its descriptor IDs) is in `collectorsByID`, and
`MustRegister` panics on the error.

## Why it was false

The descriptor ID of a descriptor without const labels is `xxhash64(fqName ++ "\xff")`
(`desc.go`, `V2.NewDesc`: the const label values with the name first, each followed by
`separatorByteSlice`). A 64-bit hash of strings has collisions, so two distinct names `n1`, `n2`
can have one ID. With both in `Ns`, the holder of `nameFree n1` registers `n1`, which registers
`n2`'s ID: `nameFree n2`'s promise is broken while it is held, and the second `MustRegister`
panics. The axiom's argument ("each right exists once ... so no name of `Ns` is registered twice")
covered the names, not their IDs, and `namesUnclaimed` only constrains code the repository does not
verify.

A colliding pair, found by a distinguished-point collision search (`/shared/tmp/promdeep/collide`,
17 s on 16 cores; about 2^32 hashes):

    m_b699caa269ad35ee   m_641c7bdac316dcb7   ID 0xfea999cc795d2229

Both are valid metric names (`nameOk`: non-empty ASCII; also the legacy regular expression).
`examples/axiomcx/promidcollide/promidcollide_test.go`: `NewCounter` of each, `MustRegister` of
the first returns, of the second panics with `AlreadyRegisteredError`. Over the axioms, the same
program (`NewCounter.spec`, `MustRegister.spec` with `nameFree n1`, `nameFree n2`) has a WP proof,
so `goose_adequacy_start` with `Ns = [n1, n2]` concluded that it does not panic.
`prometheus.descId_collision` checks the pair in Lean, over the xxhash model.

## The fix

- `Proof/github_com/cespare/xxhash/v2/Model.lean`: `xxhash.sum64`, XXH64 with seed 0 as
  cespare/xxhash v2.3.0's `Sum64` (`xxhash_other.go`), with kernel-checked test vectors from the Go
  package covering every branch.
- `prometheus.descId n := xxhash.sum64 (n ++ [0xff])`, `prometheus.descIdsDistinct Ns` (their
  pairwise distinctness, decidable).
- `goose_adequacy_start` takes `hNsIds : prometheus.descIdsDistinct Ns` (an auto-parameter,
  `decide +kernel`); so do `etcd_adequate`, `etcd_adequate_alloc` and their `_members` forms
  (`examples/lib/etcdstart/`), so the kernel checks every program's names where its closed theorem
  is proved. The closed theorems' statements are unchanged; etcd's metric names have distinct IDs.

The model's faithfulness is now part of the trust base (a definition in an axiom's premise): if
`sum64` differed from Go's hash, the check could pass on names that collide. The test vectors
(lengths 0 to 71, every branch of `Sum64`) are the evidence.
