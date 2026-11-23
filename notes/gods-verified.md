# gods verified: the treemap premise retired (EPaxos, SwiftPaxos)

Upamanyu's request (#8, 2026-11-23 18:11Z): "a slightly tweaked `gods` with the `goto`s removed,
verified, so that the `treemap.Hyps` premise retires for EPaxos and SwiftPaxos alike". Branch
`gods-verified` (off `lean` 53071bdfd5). Real goto support in goose is mit-pdos/perennial#691 (not
ours).

## The model (`models/gods`)

`models/gods` is now gods v1.18.1's own code for the packages the kits reach (`utils`, `containers`,
`maps`, `trees`, `trees/redblacktree`, `maps/treemap`), verbatim but for one file:
`trees/redblacktree/iterator.go`'s `Next` and `Prev`, whose bodies jump to the labels `between`/`end`
(`begin`) with `goto`, which goose does not translate. Until now the model was a sorted slice in place
of the tree (with `NotModelled` panics), and the kits translated the real v1.18.1 from the module cache
with `Next`/`Prev` names only. `models/diff.py gods --stat`: 1 file, +57 -58 lines; 52 upstream package
directories not in the model (packages no kit reaches).

The two `MODEL:` regions, verbatim:

```go
func (iterator *Iterator) Next() bool {
	// MODEL: gods v1.18.1's body jumps to the labels `between` (position between, return true) and
	// `end` (node nil, position end, return false) with `goto`, which goose does not translate
	// (mit-pdos/perennial#691). The same steps as structured branches: each `goto between` is the
	// label's two statements in place, each `goto end` (and the fall-through past the parent loop)
	// reaches the `end` statements after the outer `if`. The conditions, the fields read and written
	// and their order are gods'; models/internal/tpdifftest's rbt_test.go checks it against v1.18.1.
	if iterator.position != end {
		if iterator.position == begin {
			left := iterator.tree.Left()
			if left != nil {
				iterator.node = left
				iterator.position = between
				return true
			}
		} else if iterator.node.Right != nil {
			iterator.node = iterator.node.Right
			for iterator.node.Left != nil {
				iterator.node = iterator.node.Left
			}
			iterator.position = between
			return true
		} else {
			for iterator.node.Parent != nil {
				node := iterator.node
				iterator.node = iterator.node.Parent
				if node == iterator.node.Left {
					iterator.position = between
					return true
				}
			}
		}
	}
	iterator.node = nil
	iterator.position = end
	return false
}

func (iterator *Iterator) Prev() bool {
	// MODEL: gods v1.18.1's body jumps to the labels `between` (position between, return true) and
	// `begin` (node nil, position begin, return false) with `goto`, which goose does not translate
	// (mit-pdos/perennial#691). The same steps as structured branches, as in Next (mirrored).
	if iterator.position != begin {
		if iterator.position == end {
			right := iterator.tree.Right()
			if right != nil {
				iterator.node = right
				iterator.position = between
				return true
			}
		} else if iterator.node.Left != nil {
			iterator.node = iterator.node.Left
			for iterator.node.Right != nil {
				iterator.node = iterator.node.Right
			}
			iterator.position = between
			return true
		} else {
			for iterator.node.Parent != nil {
				node := iterator.node
				iterator.node = iterator.node.Parent
				if node == iterator.node.Right {
					iterator.position = between
					return true
				}
			}
		}
	}
	iterator.node = nil
	iterator.position = begin
	return false
}
```

Reason (in the regions' comments): each `goto between` is the label's two statements (`position =
between; return true`) in place; each `goto end` (`goto begin`), and the fall-through past the parent
loop, reaches the label's statements (`node = nil; position = end` (`begin`); `return false`) after the
outer `if`. The conditions, the fields read and written and their order are gods'. So the behaviour is
identical, including the panics (a nil `tree` dereferenced in `Left()`/`Right()`, a nil `node`).

The kits translate gods from the model: `module_models={"github.com/emirpasic/gods": "models/gods"}`
in `etc/dsv/epaxos.py` and `etc/dsv/swiftpaxos.py` (kit config only; `etc/goose.py` and
`etc/gen-init.py` unchanged). goose's `-modfile` route fails under goose (go/packages runs a `go list`
with `GO111MODULE=off`, which refuses `-modfile`), so each kit's module has a `go.work` (`use .`), as
dsv-quepaxa's does, and goose.py's workspace route adds the `replace`. The translation's only change is
`Dsverify/Code/github_com/emirpasic/gods/trees/redblacktree.lean` (`Iterator.Next`/`Prev` with their
bodies; the `.toml` no longer excludes them). The kits' `state` tests pass against the model.

## The differential test

`models/internal/tpdifftest/rbt_test.go` (in the gates through `run.sh`, which builds the same tests
against gods v1.18.1 from the module cache and against the model, and compares the transcripts byte
for byte): 3000 random red-black trees (118971 `Put`s and 59264 `Remove`s of random int keys, under
`utils.IntComparator` and the kits' `state.KeyComparator` on an int64 key), on each a random walk of
up to 60 steps of an iterator (`Next`, `Prev`, `Begin`, `End`, `First`, `Last`, `NextTo`, `PrevTo`;
from `tree.Iterator()`, from treemap's iterator over the same entries, and from `IteratorAt` a node),
with `Key` and `Value` (and their panics) after every step: 112138 steps, each checked against a
reference (the sorted keys and a position) and written to the transcript; 743 walks while the tree
changes under the iterator (transcript only), and the zero/empty-tree iterators. `Next` and `Prev`
are 100% statement-covered (`go test -coverpkg`). The treemap tests' former `NotModelled` cases
(changes during iteration, `Select`'s predicate changing the map, JSON) are now gods' code in both
builds and compared (`treemap-mutation.txt`). Result (2026-11-23): all transcripts equal
(`rbt-iterator.txt` 126657 lines, `treemap.txt` 313521, ...), `tpdifftest: ok`.

## The proof

`Dsverify/Proof/github_com/emirpasic/gods/` (with `Dsverify/Spec/.../trees/redblacktree/Specs.lean`
and `.../maps/treemap/Internal.lean`), about 4450 lines:

* `trees/redblacktree/Model.lean` (pure): the model tree `RB` (address, key, value, subtrees; no
  colors), contexts (`Ctx`, frames innermost first, `plug`), their entries/addresses lemmas, search
  bounds, `putE` on split lists.
* `trees/redblacktree/Defs.lean`: the heap representation and its laws.
* `Specs.lean` (rbt): `NewWith`, `Put`, `Get`, `lookup`, `Iterator`, `Left`, `Next`, `Value`, `Key`,
  `replaceNode`, `rotateLeft`/`Right`, `nodeColor`, `sibling`, `uncle`, `grandparent`,
  `insertCase1`/`4`/`5`.
* Proofs: `Iter.lean`, `Lookup.lean`, `NewWith.lean`, `Rotate.lean`, `Helpers.lean`, `Insert.lean`
  (`insertCase1` with 2 and 3 inline by Löb induction; `Put`'s search loop and both insertions).
* `maps/treemap/Rep.lean` (the concrete `isTreeMapR`, `iterValR`, `ownIterR`; the iterator law),
  `Iter.lean`, `Select.lean` (its loop over the iterator, the map whole again after the walk),
  `Results.lean`: the linked results and **`treemap.hyps_true : treemap.Hyps GF`** (no premise; the
  only class instances it uses are the program's `Assumptions` and `go.Semantics`).

**The invariant** (`isTree tr enc es`, `Defs.lean`): `tr ↦ Tree{Root: T.loc, size, Comparator: cmp}`,
the nodes `ownNodes h D` (`[∗] l ∈ D, l ↦ h l`), and the pure facts
`Rep enc h T null` (every node of the model tree `T` is at its address with key `enc k`, its value,
its children's and parent's addresses; colors are the heap's), `D` a permutation of `T`'s addresses
without duplicates, `sortedE T.entries` (the in-order entries strictly increasing: the BST order),
`T.entries = es`, `rootBlack h T` (the root is black: the only red-black fact the code's safety needs,
so that `insertCase4`/`5` find a grandparent), and `cmpOk cmp enc`. No balance invariant. The size
field is not tracked. The fix-up's specs are over `treeRaw` (the same without sortedness/root color):
rotations keep `T`'s entries and every node's color; `insertCase1`'s precondition is "the root is
black unless it is the node". Iterators: `ownIterT q tr enc cmp T h D rest cur` (the tree fixed;
`iterAt`: before the first entry, past the last, or at a node `n` with `T = plug C (node n ..)` and
`rest = R.entries ++ post C`).

Axioms: only Lean's three (below).

## The statements (both stronger: a premise removed)

**EPaxos** (`Dsverify/Spec/.../epaxosnet/TopLevelRobustness.lean`, `epaxos_remote_robust.spec`): the
premise

```lean
    (∀ (G : GooseGlobalGS HasLC.hasLC remoteGF) (L : GooseLocalGS remoteGF), letI := heapAt G L;
      github_com.emirpasic.gods.maps.treemap.Hyps remoteGF) →
```

is deleted; the proof passes `treemap.hyps_true` to `StateTreemap.ofGods`. Nothing else in the
statement changes (its header's premise list loses the treemap bullet and says why).

**SwiftPaxos** (`swiftpaxos_remote_robust.spec`, text unchanged but for the header): the treemap
was two parts of the premises the statement names, both removed:

* `SwiftLibs` (`Base.lean`, the libraries' representation choice `l`, universally quantified) loses
  the fields `isTreeMap` and `isTreeMap_sorted`; the kit's `isTreeMap` is now gods' own
  `treemap.isTreeMapR` (`lib/Treemap.lean`, `isTreeMap_sorted` proved);
* `SwiftHyps` (`Hyps.lean`, a premise at every heap) loses `treemap_NewWith`, `treemap_Put`,
  `treemap_Get`; the lab names `treemap.wp_NewWith`, `Map.wp_Put`, `Map.wp_Get` are now theorems
  from `hyps_true` (`state/Results.lean`, linking).

```diff
 class SwiftLibs (GF : BundledGFunctors) extends Net.NetProtoGS where
   gobFmt : sp.GobFmt
-  isTreeMap : HeapGS HasLC.hasLC GF → Loc → (w64 → GoInterface) →
-    github_com.emirpasic.gods.maps.treemap.Entries → IProp GF
-  isTreeMap_sorted : ∀ hG tm enc es, isTreeMap hG tm enc es ⊢
-    isTreeMap hG tm enc es ∗ ⌜github_com.emirpasic.gods.maps.treemap.sortedE es⌝
   gobEncoder : ...
 class SwiftHyps ... : Prop where
-  treemap_NewWith : ∀ [github_com.emirpasic.gods.maps.treemap.Assumptions],
-    github_com.emirpasic.gods.maps.treemap.NewWith.spec (GF := GF) isTreeMap
-  treemap_Put : ∀ [github_com.emirpasic.gods.maps.treemap.Assumptions],
-    github_com.emirpasic.gods.maps.treemap.Map.Put.spec (GF := GF) isTreeMap
-  treemap_Get : ∀ [github_com.emirpasic.gods.maps.treemap.Assumptions],
-    github_com.emirpasic.gods.maps.treemap.Map.Get.spec (GF := GF) isTreeMap
   gob_NewEncoder : ...
```

Any instance of the old premises gives one of the new (drop the fields), so the new statement implies
the old one.

## Checks (2026-11-23)

* fk-lean1 (`fklean1-check.sh`, head 312fff30bc): the six TopLevelRobustness modules (swiftnet,
  epaxosnet, rabianet, quepaxanet, paxosnet, Net's remote counter) build; `#print axioms` of
  `swiftpaxos_remote_robust`, `epaxos_remote_robust`, `rabia_remote_robust`, `quepaxa_remote_robust`,
  `paxos_remote_robust`, `counter_remote_robust` and `treemap.hyps_true`: `[propext,
  Classical.choice, Quot.sound]` each.
* Here: `etc/tier-check.py --check` ok (227 known, no new); `etc/gen-init.py --check` ok (271 files;
  gods' `Init.lean`s unchanged: their initializers are gods' and were translated before);
  `etc/goose.py --check` ok (all 71 projects); `etc/copy-part.py --check` 0 differ;
  `proof_roots.namespace()` = `Perennial.EtcdGrove.` (as on `lean`); the dup scan: no new names (the
  4 hits are the scan's pre-existing false positives); `git diff <base> -- etc/goose.py
  etc/gen-init.py` empty (gods' settings are in `etc/dsv/{epaxos,swiftpaxos}.py`).
* `models/internal/tpdifftest/run.sh`: ok.
