# Files of the etcd-io/etcd#22243 verification

The report is `notes/pr-verify/etcd-22243.md`. Revisions:

- PR head: etcd-io/etcd `31530b6b4bedd91b824cdfbb9f64f002bcd33773` (fetched as `pr-etcd-22243`);
- upstream base: `a279d15ac644f8420120673659110d07ef33a554` (the PR's merge base with `main`);
- verified fork: `mit-pdos/etcd-grove` branch `pr-etcd-22243-goose-lean` (`aa7d61874`: the PR on
  the fork's `goose-lean` `09669450f`, plus a blank import of `net/url`).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `corrupt_bodybound_test.go` | The body bound at its edge and on a large body: with the PR, a 64 KiB body is served (200), one byte more gets 413, and of a 16 MiB body the handler reads 65537 bytes; on the base, every body is served and read whole. This is the spec's `bodyClosed (c.drop (min len (65536 + 1)))` and the 413 case. | PR head and base (package `etcdserver`) | `cp corrupt_bodybound_test.go <etcd>/server/etcdserver/ && cd <etcd>/server && go test ./etcdserver/ -run TestHashKVHandlerBodyBound -v` |
| `bodybound-up-head.log` | That test's output at the PR head: passes. | PR head | as above |
| `bodybound-up-base.log` | That test's output at the base: fails (200 for the oversized bodies, 16777216 bytes read). | base | as above |
| `axioms-hashKVHandler.wp_ServeHTTP.txt` | The spec-level axioms (`*.wp_proof` and the axiomatized predicates) the linked result `hashKVHandler.wp_ServeHTTP` rests on, filtered from `#print axioms` (the rest of the output is the axiomatized types and package-init values of the translation, as for every server result). No `sorryAx`. | this branch | `lake env lean notes/pr-verify/etcd-22243/PrintAxioms.lean` (after `lake build Proof.go_etcd_io.etcd.server.v3.etcdserver.Link`), then `grep 'wp_proof\|EtcdGrove\.\(http\|json\)\|idStr'` |
| `PrintAxioms.lean` | The `#print axioms` command used above. | this branch | as above |

The probe calls `ServeHTTP` directly with a counting body whose `Close` does nothing, so it
measures the handler's own reads, not net/http's drain of the connection on `Close`.

Go commands use `GOTOOLCHAIN=go1.27.1`.
