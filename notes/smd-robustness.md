# The structured-merge-diff driver's robustness theorem (2026-11-19)

Goal: a closed `Robustness.Robust` theorem about `examples/k8s/smd` (`Main`: nine server-side apply
and update steps through structured-merge-diff's `merge.Updater.Apply`/`Update`, each checked
against the expected object, managed fields and conflicts, with a panic on any difference), so that
"no panic" means SMD computes exactly those results. This stage: the plumbing and the statement,
building, with `Main.wp_proof` a `sorry`. SMD's translation: `notes/smd-goose.md`.

## The statement

`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/smd/TopLevelRobustness.lean` (the file to audit):

    def smd_driver_robust.spec : Prop :=
      ∀ [lctx : GoLocalContext] [sem : go.Semantics]
        [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions] (σ : state)
        (g : GlobalState) (bound : Nat),
        Robustness.Robust [] [(smdProgram, σ)] g bound

with the trivial extension (`attribute [local instance] trivialExts ...`), and the program
(`Proof/.../k8s/smd/TopLevelDefs.lean`):

    def smdProgram : Expr :=
      Seq (App (Val github_com.mit_pdos.etcd_grove.examples.k8s.smd.initialize') (Val #()))
        (App (App (Val (GoInstruction (FuncResolve github_com.mit_pdos.etcd_grove.examples.k8s.smd.Main []))) (Val #())) (Val #()))

One machine that never crashes runs the driver's initialization (SMD's five packages and the
standard library's they import) and then `Main()`, a fresh Go process (`Robust`'s premise); for any
Go semantics and package assumptions, in every execution of fewer than `bound` steps no thread is
stuck and none has an unrecovered panic.

- **The bound**: any (a parameter), as `goose/prophkv`'s: `Main.spec` takes no receipt or thread
  bound, so `goose_adequacy` runs at `N = n + 1`, `T = n + 2` for every `n`. If the proof of `Main`
  turns out to need one (a counter that must not wrap), the statement takes the bound it needs.
- **`Main.spec`** (`Spec/.../k8s/smd/Main.lean`), as prophkv's:

      abbrev Main.spec : Prop :=
        {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd }}
          (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.smd.Main)) (Val #()))
        {{ RET #(); True }}

  at `HeapGS HasLC.hasLC GF`. Returning normally is the whole guarantee: every check of the
  driver is a panic.

## The files

- Translation: project `k8s-smd` of `etc/goose.py` (`local="examples/k8s/smd"`, the driver's own
  Go module, lean roots `sigs.k8s.io/structured-merge-diff/v7=` and `github.com/mit-pdos/etcd-grove=`,
  so the driver's module imports project `smd`'s `Code.sigs_k8s_io...` modules);
  `Code/github_com/mit_pdos/etcd_grove/examples/k8s/smd.{lean,toml}`, `GeneratedProof/...`.
  `etc/goose.py --check` now also checks `GO_MOD_TAG_PINS`: the driver's `go.mod` must require
  `sigs.k8s.io/structured-merge-diff/v7` at project `smd`'s `tag` (`v7.0.0`, the tag of its `rev`
  `8d11054b`) and must not replace it (SMD is required at a tag, so `GO_MOD_PINS`' pseudo-version
  check does not apply).
- Package facts: `Proof/sigs_k8s_io/structured_merge_diff/v7/{value,schema,fieldpath,typed,merge}/
  Base.lean` and `Proof/.../k8s/smd/Base.lean`, every fact `True` (nothing reads a package variable
  yet). `etc/gen-init.py` (`SPECIAL[_SMD + ...]`, root `...examples.k8s.smd`, `PROGRAMS` entry)
  generates their `Init.lean` and the program's `PkgTable.lean`. The translated initializers are
  stepped (`errors.New` by Perennial's `wp_New_errorString`, slice literals, `[]byte` conversions,
  the walker pools' `sync.Pool` literals after `recv_eq_func_mk`, `merge`'s `var _ error =
  Conflicts{}`); the untranslatable ones are `TrustedCode` no-ops (`notes/smd-goose.md`). **No
  axiom was added for the initializers.** The program's initialization does run `reflect`'s
  existing generated `Proof/reflect/Init.lean`, whose trust-boundary axiom
  `Perennial.reflect.opaqueInitsOk` (already in the baseline, bbolt's and raft's too) is in the
  trust base.
- Link: `etc/gen-link.py --k8s-smd` from `etc/link-lean-first-k8s-smd.txt` (namespace `k8s_smd`).
- Closed theorem: `Proof/.../k8s/smd/Results.lean`, `smd_driver_safe` (the result is `#()`, no
  thread stuck, none with an unrecovered panic), from Perennial's `goose_adequacy` directly, as
  prophkv's, with the generated `wp_initialize'` at the generated table's `getIsPkgInit_wf`. (Not
  through `init_adequate`: its module, `examples/lib/etcdstart/Adequacy.lean`, imports the etcd
  server's start rights, prometheus, the WAL and bbolt invariants; the proof is the same few lines.)
- `Proof/.../k8s/smd/TopLevelRobustness.lean`: `smd_driver_robust`, by `Robust.of_single`.
- Trust base: `etc/tcb-collections/smd.txt`.

## What is trusted

`etc/tcb-report.py --collection etc/tcb-collections/smd.txt`:

- `sorry k8s_smd.Main.wp_proof`;
- the standard library as SMD calls it (names-only in Perennial), trust-boundary axioms whose spec
  files say why each is true of Go (go1.27's source quoted):
  - `reflect.DeepEqual.wp_proofNil` (`Spec/reflect/DeepEqualNil.lean`): `DeepEqual(nil, nil)` is
    `true`. `schema.StructField.Equals` compares the fields' `Default`s with it; the driver's schema
    has none. A second spec beside bbolt's `spec_pgidSet`, in a file of its own so that SMD does
    not import bbolt (gen-link's `reflect_DeepEqual+Nil`);
  - `slices.BinarySearchFunc.wp_proof`: for a `cmp` that on each element returns a pure `c e` and
    keeps a resource, with signs non-decreasing along the slice, the least index with `c ≥ 0` and
    whether `c = 0` there;
  - `slices.Insert.wp_proof`: `Insert(s, i, v...)` holds `s[:i] ++ v ++ s[i:]`, with its capacity
    (`s`'s ownership given up);
  - `sort.SliceStable.wp_proof`: with a `less` deciding a strict weak order, a sorted permutation
    (stability not stated);

  linked in the driver's `Link.lean` so that the collection lists them; their users are SMD's
  functions' proofs, not written yet;
- `Perennial.reflect.opaqueInitsOk` (above).

`etc/tcb-baseline.txt` has the four axioms and the `sorry` added by hand (its `--check --update`
needs the whole repository built; the collection's was run on the driver's roots only).

## What remains

- **Specs of SMD's API** the driver calls, then `Main.wp_proof` taking them: `typed.AsTyped`,
  `value.NewValueInterface` (of `map[string]interface{}`, `[]interface{}`, `string`, `int64`),
  `merge.UpdaterBuilder.BuildUpdater`, `merge.Updater.Apply`/`Update` (the object and managed fields
  each step produces, `Conflicts` on step 4), `typed.TypedValue.AsValue`, `value.Equals`,
  `fieldpath.ManagedFields.Equals`, `fieldpath.NewSet`/`NewVersionedSet`/`MakePath`-style path
  builders, `merge.Conflicts.Equals`, and the error interface assertion `err.(merge.Conflicts)`.
  Their proofs cover the 311 SMD functions of `notes/smd-goose.md`'s table, over the four
  stdlib axioms above and Perennial's `sync.Pool`, `sync.Once`, `atomic.Pointer`, `fmt`, `errors`,
  `strings`, `sort.Strings` specs.
- **Package facts**: the proofs will need what the variables hold (`value.HeapAllocator`,
  `EmptyRange`, `fieldpath.ErrUnknownPathElementType`, `typed`'s walker pools and `ruleKeepRHS`):
  facts in the `Base.lean`s and the `finish` steps in `etc/gen-init.py`'s `SPECIAL` entries.
- `SpecPlan/Spec/PkgInit/` (`etc/gen-specs-pkginit.py --check`) does not have SMD's or the driver's
  files (SMD's were already missing before this stage; not regenerated here).
