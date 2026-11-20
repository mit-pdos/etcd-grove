# k8s 7g follow-up (B'): handoff

## START HERE

Brief: `notes/k8s-7g-listaccessor-bprime.md` (approved by the user to start after wal-fsfix). Context:
`notes/k8s-7g-trust.md` §11-§12. Worktree `/shared/etcd-grove-bprime`, branch `k8s-bprime` off lean
`cd4e31df13`; manifest `/shared/tmp/manifest-c44.json`, `PERENNIAL_DIR=/shared/perennial-c44b74871`;
`.lake/build` seeded from `/shared/etcd-grove-k8sunified` (built at `f7f4930794`). Scratch:
`/shared/tmp/bprime/`. The k8s closed theorems are one now: `k8s_safe`/`k8s_robust`
(`examples/k8s/all`, collection `etc/tcb-collections/k8s-all.txt`); they must stay textually unchanged.

State:
- Step 1 done (uncommitted -> committed with the drafts): the Goose configuration of
  `/shared/tmp/k8s7g/goose-la.patch` (meta's `ListAccessor` with its body, `ListMeta.GetResourceVersion`/
  `GetContinue`, the four typed lists' promoted methods); `etc/goose.py --project k8s-apiserver
  --perennial /shared/perennial-c44b74871` reproduces the patch's generated files exactly (0 updated).
- Step 2 drafted, NOT proved: `Spec/k8s_io/apimachinery/pkg/api/meta/ListAccessor.lean` restated in
  `Accessor.spec`'s shape (STOP: trusted text; awaiting the coordinator). The axiom file
  `Proof/.../meta/ListAccessor.lean` is unchanged until approval.
- Step 4 designed, NOT implemented: `Spec/k8s_io/client_go/tools/cache/typedListMeta.lean` (the pending
  hypothesis; STOP: awaiting the coordinator).

Next, once approved: prove `ListAccessor.wp_proof` (as `Accessor.wp_proof`); the three 7g callers
(`go_type_set` for `*ObjList`); pager/reflector over `typedListMeta.spec`; link list entries
(`typedListMeta: ?`, callee of `pager_ListPager__list` and `Reflector__list`); gen-link
`--k8scache`/`--k8setcd3`/k8s-all modes; land path (brief "Stops", coordinator's message).
