# k8s 7g follow-up (B'): prove `meta.ListAccessor` (brief; not started)

Decided by etcd-grove-03 (2026-11-19): a follow-up AFTER 7g lands. Goal: remove the axiom
`apimeta.ListAccessor.wp_proof` from the 7g closed theorems (`k8s_etcd3_safe`, `_cluster_safe`,
`_partition_safe`) without adding trust. Background: `notes/k8s-7g-trust.md` §11; questions.md
"Night 22".

## Why the spec as stated cannot be proved and linked

`Spec/k8s_io/apimachinery/pkg/api/meta/ListAccessor.lean`'s first row (`listAccOk` of a typed list
`*v1.PodList`, ...) is about `k8s.io/api/{core,apps}/v1` code (the promoted `ListMeta` methods),
whose `Assumptions` neither the k8s driver's Link nor client-go cache's reaches; adding them changes
the closed statements' instance list (a closed-statement change). The second row (`*ObjList`) is
provable.

## The plan

1. Translate `meta.ListAccessor` with its body (and `ListMeta.GetResourceVersion`/`GetContinue`):
   the patch is ready, `/shared/tmp/k8s7g/goose-la.patch` (Goose configuration; `etc/goose.py
   --check` passed with it on night 22). Re-run `etc/goose.py --project <k8s project>`.
2. Restate `ListAccessor.spec` IN PLACE (no twin) in `Accessor.spec`'s shape: for any value in
   `List`'s type set (the value itself, and `nil`), the type switch's first case returns the same
   interface value and a nil error. Provable from the body with `meta`'s `Assumptions` only.
   Replace the axiom in `Proof/k8s_io/apimachinery/pkg/api/meta/ListAccessor.lean` by the proof.
3. Callers in 7g (`Proof/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/correctness/`):
   `Model__listResponseRV`, `Model__equalListResponse`, `Replay__validateList`: give `*ObjList`'s
   membership in `List`'s type set (`go_type_set`), then use the methods as before.
4. The reflector (`Proof/k8s_io/client_go/tools/pager/ListPager__list.lean`,
   `Proof/k8s_io/client_go/tools/cache/Reflector__list.lean`): the typed lists' facts
   (what `listAccOk` says today) become a pending hypothesis of the reflector's results
   (not a Go function's spec: gen-link and `--layout` need a convention for it; design it first
   and report it). The cache's `Link` then has that hypothesis in place of `ListAccessor.spec`.
5. Trust base: `etc/tcb-report.py --check --update` (-1 axiom in the baseline, `k8setcd3.txt` -1,
   `clientgo-cache.txt`: the axiom replaced by the new hypothesis); interfaces; gen-link modes.

## Stops

- Step 2 is a change to trusted text (an axiom goes, a spec restated): report the restated spec
  before proving.
- Step 4's new pending hypothesis is a change to the cache's results' premises: report its design.
- The 7g closed statements must stay textually unchanged; if they cannot, stop.

Estimate (night 22): more than a day, mostly step 4 (a design change on the reflector track).
Go evidence to keep: `examples/k8s/etcd3/trustspecs_test.go` `TestListAccessorObjList`.
