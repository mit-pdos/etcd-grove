# dsv-json-main: the Dsverify kits on the main tree's encoding/json (2026-11-23)

Branch `dsv-json-main`, off `lean` 7cab534fb7 (J1 of mit-pdos/etcd-grove#24 landed:
`Code/encoding/json.lean` is the model's names, `Proof/encoding/json/Base.lean` its package fact,
`Proof/encoding/json/Init.lean`'s `wp_initialize'` proved with no axiom). The coordinator's
decision: Dsverify keeps no copy of encoding/json; the kits move onto the main tree's.

## What changed

Users of Dsverify's encoding/json on `lean`: the epaxos and swiftpaxos kits (and, through them,
gods' red-black tree and orcaman/concurrent-map, whose translations import encoding/json). No
other landed kit (paxos, rabia, quepaxa) and nothing in `Net/` uses it. Neither kit uses any
encoding/json spec (only the package's initialization), so there was no spec to move.

- `etc/dsv/epaxos.py`, `etc/dsv/swiftpaxos.py`: lean root `encoding/json=` (was `=Dsverify`);
  `encoding/json` dropped from `packages` and `owned` (std_models keeps it: the kits' code
  is translated against the model's API, as the main tree's is); `encoding.json` out of
  `HYP_INITS`, into `MAIN` and `MAIN_GEN`.
- Translations regenerated (`etc/goose.py`): the redblacktree, concurrent_map and both replicas'
  `Code`/`GeneratedProof` import `Code.encoding.json`/`GeneratedProof.encoding.json` (the only diff).
- Deleted: `Dsverify/Code/encoding/json.{lean,toml}`, `Dsverify/GeneratedProof/encoding/json.lean`,
  `Dsverify/Proof/encoding/json/Base.lean`, and the hand-written hypothesis
  `Dsverify/Proof/encoding/json/Init.lean` (class `encoding.json.InitHyp`).
- `Dsverify/Proof/encoding/json/Init.lean` is now **generated** (`etc/gen-init.py`, `MAIN_GEN`): the
  main tree's `Init.lean` over `Net/`'s `PkgInitExt`, exactly as `Dsverify/Proof/bufio/Init.lean`. It
  cannot be avoided: the main tree's `Init` imports `Proof.runtime.PkgInitExt`, which declares the
  same names as `Net.Proof.runtime.PkgInitExt` that every Dsverify closure imports. It imports the
  main tree's `Proof.encoding.json.Base` (the fact) and declares no name of its own beyond the
  main tree's `wp_initialize'`/`wp_initialize'_lb` (not in any Dsverify closure together; dups.py
  clean).
- gen-init's generated `Init`/`PkgTable` files lose `[encoding.json.InitHyp GF]` and call
  `encoding.json.wp_initialize'_lb`. Hand-written `Base.lean` files import
  `Proof.encoding.json.Base` instead of the json `Init`. `etc/dsv/_swiftpaxos_boot.py` and
  swiftnet's `BootLinked.lean`/`BootCmdsLinked.lean` drop the section variable.
- The two statements and their proofs (below); `etc/tcb-collections/dsv-epaxos.txt`'s comment.

## Statement diffs (premises only removed)

`Dsverify/Spec/github_com/imdea_software/swiftpaxos_epaxos/examples/epaxosnet/TopLevelRobustness.lean`,
`epaxos_remote_robust.spec`:

    -    (∀ G L, letI := heapAt G L; encoding.json.InitHyp remoteGF) →

`Dsverify/Spec/github_com/imdea_software/swiftpaxos/examples/swiftnet/TopLevelRobustness.lean`,
`swiftpaxos_remote_robust.spec`:

    -    (∀ G L, letI := heapAt G L; encoding.json.InitHyp netDistGF) →

plus each file's header (the premise list) and the dropped import of the json `Init`. No other
statement changed; rabia, quepaxa, paxos and remote counter untouched.

## Checks

- fk-lean1 (`/shared/tmp/fklean1-check.sh`, head 5a3d4e24e5 with the scratch module
  `Dsverify/Scratch/Axioms.lean`, deleted after): the six `TopLevelRobustness` modules (swiftnet,
  rabianet, epaxosnet, quepaxanet, paxosnet, Net's remote counter) and the scratch module importing
  all six together: `Build completed successfully (4797 jobs)`, no error. `#print axioms` of
  `swiftpaxos_remote_robust`, `rabia_remote_robust`, `epaxos_remote_robust`, `quepaxa_remote_robust`,
  `paxos_remote_robust`, `counter_remote_robust`: each exactly `[propext, Classical.choice, Quot.sound]`.
- Here: `etc/tier-check.py --check` ok, 227 known violations (as `lean`); `etc/gen-init.py --check`
  272 files up to date (run twice before); `etc/goose.py --check --project dsv-epaxos --project
  dsv-swiftpaxos` up to date; `etc/dsv/_swiftpaxos_boot.py --check` ok; `etc/copy-part.py --check`
  0 differ; `proof_roots.namespace()` = `Perennial.EtcdGrove.`; dups.py: 4 hits, all regex false
  positives (`inductive`/`is`/`of`/`per` in comments), none about encoding/json;
  `git diff origin/lean -- etc/goose.py etc/gen-init.py` empty.

## What dsv-vr must change (not done here)

dsv-vr (0fc08fe7dc) has its own copies of the deleted files, identical to `lean`'s, so a merge
deletes them cleanly; then:
- `etc/dsv/vr.py`: `"encoding/json="` (not `=Dsverify`); drop `"encoding/json"` from `packages` and
  `owned`; `HYP_INITS = []`; `MAIN`/`MAIN_GEN` += `'encoding.json'` (as epaxos/swiftpaxos here).
  Rerun `etc/goose.py --project dsv-vr` and `etc/gen-init.py` (twice).
- Its hand-written imports of `Dsverify.Proof.encoding.json.Base` -> `Proof.encoding.json.Base`;
  of `Dsverify.{Code,GeneratedProof}.encoding.json` -> the main tree's; the json `Init` path stays
  (now generated).
- Its `Spec/jsonlib.lean` (`Dsverify/Proof/github_com/tangledbytes/go_vsr/Spec/jsonlib.lean`) and the
  bufio helper in `Proof/events/LibHyps.lean` duplicate J1's `Proof/encoding/json/Registry.lean`
  (`codecSetWith`, `codecFnsWith`, `codecOkWith`, `EncoderRep`, `DecoderRep`, `isSpaceB`; generic in the
  codec's functions, so VR's `codecSet`/`kitCodecOk` become instances at its codec), `Proof/bufio/ErrOrNil.lean`
  and `Spec/encoding/json/Codec/{Unmarshal,NewEncoder,Encoder__Encode_conn}.lean`: delete VR's and use the
  main tree's. If a main-tree shape differs from VR's (e.g. a stronger premise), that is a statement
  change for the coordinator.
- Its `TopLevelRobustness` drops `(∀ G L, letI := heapAt G L; encoding.json.InitHyp remoteGF) →` (and
  `hji`), as here.
