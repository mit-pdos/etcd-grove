# `clientv3.streamKeyFromCtx` and `streamKeyOf`'s laws (G2's (c), 2026-10-30)

**Reviewed** at `7ec9f1f715` (branch `g2-stmts`; diff against `8527537fba`; design
`notes/g2-watch-auth.md`, "Trusted statements changed", row (c)):

- `streamKeyFromCtx.wp_proof` (`Proof/go_etcd_io/etcd/client/v3/streamKeyFromCtx.lean`, its triple
  `Spec/go_etcd_io/etcd/client/v3/streamKeyFromCtx.lean`): at a context (`context.isContext ctx cd`),
  returns `streamKeyOf (metadata.outgoingOf ctx)`;
- `streamKeyOf_none` and `streamKeyOf_single` (`Proof/go_etcd_io/etcd/client/v3/StreamKey.lean`),
  over the opaque `streamKeyOf : GrpcMd → GoString`;
- with the other axioms that constrain `outgoingOf` (`Proof/google_golang_org/grpc/metadata/
  Outgoing.lean`): `metadata.AppendToOutgoingContext.wp_proof` (`mdAdd`), `withVersion.wp_proof`
  (`mdSet`), `WithTimeoutBackgroundMd` (`none`), `WithCancelValCtx` (keeps it), authkv's `reqCtx`.

Go: etcd fork at `249d76bea7` (`etc/goose.py`, `.lake/go-src/etcd`), grpc-go v1.84.0 (etcd's
`client/v3/go.mod`), toolchain go1.27.3 (`GO_TOOLCHAIN`). `streamKeyFromCtx` is
`client/v3/watch.go:1102-1107`; `FromOutgoingContext` grpc `metadata/metadata.go:331-361`,
`AppendToOutgoingContext` `:250-263`, `NewOutgoingContext` `:243-245`.

## Verdict

| axiom | verdict |
|---|---|
| `streamKeyFromCtx.wp_proof` | **ok** for every context the repository's specs build; one margin (below, attack 6), documented in part |
| `streamKeyOf_none` | **ok**: true of Go's printer and consistent |
| `streamKeyOf_single` | **refuted jointly with `metadata.AppendToOutgoingContext.wp_proof`** (non-ASCII keys: the two together predict different keys where Go computes equal ones); and **false of Go's printer at `v = ""`** (latent: no spec builds the other side). Consistent as a logical statement (a model exists). |

The root of the joint refutation is not the law but `metadata.lowerKey` (ASCII-only "no upper-case
letter"), which `AppendToOutgoingContext.spec` takes as the premise under which grpc keeps the key
as given: grpc lower-cases with `strings.ToLower`, which is Unicode case mapping (and replaces
invalid UTF-8 by U+FFFD). So the spec's postcondition `outgoingOf c' = mdAdd .. k v` is false of Go
for a key like `É`; `streamKeyOf_single` (whose premise is the same `lowerKey`) is the law that
makes the false postcondition observable in `streamKeyFromCtx`'s result.

No Goose counterexample program: `streamKeyFromCtx` is unexported, so no program outside `clientv3`
calls it, and no exported spec (`watcher.Watch`, `watcher.RequestProgress`) exposes the key in a
way a program can check (they say which stream a watch joins, not anything a Go program observes).
The refutation is therefore (i) Go tests, one calling the fork's own `streamKeyFromCtx`, and (ii) a
Lean theorem, with no `sorry`, that the axioms' postconditions entail different keys for the same
two contexts.

## The counterexample

**Go** (`examples/axiomcx/g2streamkey/g2streamkey_test.go`; `key` is `streamKeyFromCtx`'s body
verbatim, over grpc's public API):

```go
c1 := metadata.AppendToOutgoingContext(context.Background(), "É", "v")
c2 := metadata.AppendToOutgoingContext(context.Background(), "é", "v")
if key(c1) == key(c2) { panic("streamKeyOf_single: keys of {É:[v]} and {é:[v]} differ") }
```

```
$ GOTOOLCHAIN=go1.27.3 go test -v ./axiomcx/g2streamkey/        (in examples/)
    g2streamkey_test.go:35: "É" -> "map[é:[v]]" ; "é" -> "map[é:[v]]"
    g2streamkey_test.go:35: "K" -> "map[k:[v]]" ; "k" -> "map[k:[v]]"     (KELVIN SIGN, E2 84 AA)
    g2streamkey_test.go:35: "\xff" -> "map[�:[v]]" ; "�" -> "map[�:[v]]"
    g2streamkey_test.go:40: recovered: streamKeyOf_single: keys of {É:[v]} and {é:[v]} differ
```

The same against the fork's own unexported function (an internal test, `client/v3/
streamkey_axiom_test.go`, in a scratch copy of the pinned tree `git archive 249d76bea7`; not
committed to the fork):

```go
c1 := metadata.AppendToOutgoingContext(bg, "É", "v")
c2 := metadata.AppendToOutgoingContext(bg, "é", "v")
if streamKeyFromCtx(c1) == streamKeyFromCtx(c2) { panic("keys of {É:[v]} and {é:[v]} differ, by the axioms") }
```

```
--- FAIL: TestStreamKeyAxiom (0.00s)
    streamkey_axiom_test.go:14: "map[é:[v]]" "map[é:[v]]"
panic: keys of {É:[v]} and {é:[v]} differ, by the axioms [recovered, repanicked]
```

**Lean** (`Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/g2streamkey/Main.lean`):
`lowerKey_kU : metadata.lowerKey [0xC3, 0x89]` (`É` meets `AppendToOutgoingContext.spec`'s
premise), and

```lean
theorem streamKeys_differ (bg c1 c2 : GoInterface)
    (hbg : metadata.outgoingOf bg = none)
    (h1 : metadata.outgoingOf c1 = metadata.mdAdd (metadata.outgoingOf bg) kU v)
    (h2 : metadata.outgoingOf c2 = metadata.mdAdd (metadata.outgoingOf bg) kL v) :
    streamKeyOf (metadata.outgoingOf c1) ≠ streamKeyOf (metadata.outgoingOf c2)
```

`h1`/`h2` are `AppendToOutgoingContext.spec`'s postconditions for the two calls (`hbg`: a context
with none, as `WithTimeoutBackgroundMd` gives); `streamKeyFromCtx.spec` returns exactly the two
sides. `#print axioms streamKeys_differ` (`lake build` of the module, 2026-10-30): `[propext,
Perennial.EtcdGrove.streamKeyOf_single]` — nothing else. Not a triple of a Goose program (the function
is unexported, above); the Go side is the internal test.

**What rests on it.** No proof uses either law yet (`grep streamKeyOf_single`: only
`StreamKey.lean`); they are for G2's client proof (`notes/g2-watch-auth.md`, "anon"/"tok" cases,
`watchCheckOk_tok`). The consequence there is benign in Go (`É` and `é` metadata are the same
metadata after grpc's lower-casing, so sharing a stream is right), but the law as stated lets a
proof conclude `mdVals m "É" = ["v"]` of a stream whose Go metadata has no key `É`.

## Proposed restatements (not applied: trusted statements, the user's)

1. **`metadata.lowerKey`: ASCII and not upper case**, so that `strings.ToLower k = k` (Go's
   `ToLower` takes its ASCII fast path, which changes only `A`-`Z`):

   ```lean
   def lowerKey (k : GoString) : Prop := ∀ b ∈ k, b.toNat < 128 ∧ ¬ (W8 65 ≤ b ∧ b ≤ W8 90)
   ```

   Fixes `AppendToOutgoingContext.spec`, `streamKeyOf_single` and `credsMapIs`
   (`Proof/google_golang_org/grpc/InvGrpc.lean:970`, whose key fact rests on grpc's `ToLower` in
   `http2Client.getTrAuthData`, the same issue). Every current use is an ASCII literal (`token`,
   `client-api-version`, authkv's `reqCtx` by `decide`), so the callers' obligations still close.
2. **`streamKeyOf_single`: a non-empty value**, `(hv : v ≠ [])`. Go prints `[]string{}`, `nil` and
   `[]string{""}` all as `[]` (`TestEmptyValue`: `AppendToOutgoingContext(bg, "k", "")` and
   `NewOutgoingContext(bg, MD{"k": {}})` both key as `map[k:[]]`), so for `v = ""` the law claims
   `mdVals {k:[]} k = [""]`, false of Go's printer. Latent: no spec builds a context whose metadata
   has a key with no values (`mdAdd` adds one value, `withVersion`'s `mdSet` sets `[v]`; there is no
   `NewOutgoingContext` spec). With `v ≠ ""` the law is true of the printer: the target
   `map[k:[v]]` has no space, so `m` has at most one entry and it one value or none; it has exactly
   one `:` (none in `k`, `v`), so `m`'s single key is `k` (a key printed before the only `:`); the
   rest `[v]` with `v` non-empty and space-free is one value `v`. The docstring's argument ("one
   entry with one value") skips the empty list. G2 applies the law to a context's token value
   (authkv's `reqCtx` appends a fixed literal `badToken`; etcd's own per-RPC credentials send no
   token when it is empty, `client/v3/credentials/credentials.go:73`, but those are not the
   context's outgoing metadata), so the premise should cost the client proof only a literal's
   `decide`; to be checked when the proof uses the law.

## Attacks tried

1. **Nil context.** `isContext` is over `GoInterfaceOk` (a non-nil interface); the old `True`
   precondition's latent bug (audit row) is fixed. No attack.
2. **No outgoing metadata.** Go returns `""`; the spec returns `streamKeyOf none`, which no axiom
   pins to `""` but law 1 separates from every `some _`. Go: an empty or nil `MD` given to
   `NewOutgoingContext` prints `map[]` (`TestNone`), so `some` never prints as `none` does. Law 1
   **holds**. (`ok` is true whenever a `rawMD` is present, even `rawMD{md: nil}`.)
3. **Appended pairs.** `FromOutgoingContext` copies `raw.md` (lower-cased) then appends each
   `added` pair's value after (`:343-358`); `mdAdd` appends `v` after the existing values: same
   order. Key order: `%v` of a map sorts keys (`internal/fmtsort`), values in slice order, joined by
   spaces (`TestMerge`: `NewOutgoingContext(MD{b:[1], a:[x y]})` then `Append(b,2,A,z)` gives
   `map[a:[x y z] b:[1 2]]`). `%+v` and `%v` agree for `map[string][]string`. The return is a
   function of the merged map, hence of `outgoingOf` as the model reads it. **Holds.**
4. **Case.** ASCII upper case is excluded by `lowerKey`; non-ASCII case and invalid UTF-8 are not:
   **the refutation above.** Raw `MD` keys equal up to case (only via `NewOutgoingContext` with a
   literal map): grpc keeps whichever the map iteration gives last, so two calls may differ; the
   spec's docstring excludes it and no spec builds such a context. Not attackable.
5. **Law 2 against the printer.** Multi-value (`[a b]` vs `[a, b]`), keys or values with `:`, `[`,
   `]`, spaces: all excluded by the premise `hs` (checked by the colon-count argument above).
   Empty value: **false of Go at `v = ""`** (restatement 2), latent.
6. **A context whose `Value` is not a function of its interface value.** `isContextDef` (Perennial
   `context/Base.lean:481`) specifies `Value` only at `&cancelCtxKey`, so a program could define a
   context type whose `Value(mdOutgoingKey{})` alternates between `Append(ctxA, ..).Value(k)` and
   `ctxA.Value(k)` (both agree at `cancelCtxKey`) and prove `isContext` of it; Go then returns
   `""` and `map[...]` on two calls, where the spec returns one value. This is the margin the
   docstring states ("it assumes `Value(mdOutgoingKey{})` returns"), but returning is weaker than
   what the spec uses, a deterministic `Value` there (`outgoingOf` is a function of the interface
   value; the same caveat as `notes/axiom-review/withtimeout-md.md`). Not built: the counterexample
   needs `streamKeyFromCtx` (unexported) and a Goose-translated custom context with its `isContext`
   proof; the exported `Watch` spec makes nothing observable of it. Suggested docstring sharpening:
   "assumes `Value(mdOutgoingKey{})` returns, and the same `rawMD` on every call (true of grpc's and
   the `context` package's contexts)".
7. **Joint consistency.** `streamKeyOf` appears in no other axiom, so the laws cannot make the
   others inconsistent; a model: `streamKeyOf none = ""`, `streamKeyOf (some f) = "map[k:[v]]"` if
   `f` is `mdAdd none k v`'s function for some `k`, `v` meeting the premises (unique by the colon
   argument), else `"map[]"`. Both laws hold of it. The laws are consistent; the joint failure is
   with Go, not `⊢ False`.

## Other findings

- `issues/etcd-watch-stream-key-collision.md` extended: the collision needs no space (an empty
  value list and `[""]` key alike). No new `issues/` file: grpc's lower-casing is documented.
- The fault is the repository's (`metadata.lowerKey`'s reading of "lower-case"), not Perennial's.
