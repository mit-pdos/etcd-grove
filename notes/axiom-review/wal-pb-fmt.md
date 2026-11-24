# Axiom review: the WAL's protobuf trust boundary (walpb.Snapshot, walpb.Record, cached MarshalAppend)

2026-11-21. Checkout `/shared/etcd-grove-walns` (branch `wal-nostorageok`, `24829ac036`), read only.
protobuf-go v1.36.12, go1.27.3, etcd fork `d7c7f6434abc` (examples/go.mod's pin), raft fork `d2c16c558247`.
Tests: `examples/stdlib/walpb/` (`snapshot_adv_test.go`, `record_clone_test.go`, adopted from the review;
run with `go test ./stdlib/walpb/` from `examples/`). No Lean build (per instructions): the
Lean side is argued from the source text.

## Verdicts

| Axiom | File | Verdict |
|---|---|---|
| `snapEncC_ok` | `Proof/go_etcd_io/etcd/server/v3/storage/wal/walpb/PbSnapshot.lean:72` | **sound** (no counterexample); the evidence it cites does not cover its whole premise. My adversarial test now does, and passes |
| `pbSnapC_reg` | same file, :305 | **sound**: the only registration at `walpb.Snapshot.ty`. Every generic proto spec it enrolls the type in holds at Snapshot (tested) |
| `pbRecordC_reg` | `.../walpb/PbRecord.lean:202` | **sound**: the only registration at `walpb.Record.ty`. The enrolled specs hold, including the nil-versus-empty `Data` distinction |
| `proto.MarshalAppendCachedRecord.wp_proof` | `Proof/google_golang_org/protobuf/proto/MarshalAppendCachedRecord.lean` (spec in `Spec/.../MarshalAppendCachedRecord.lean`) | **sound**, with one caveat: a theoretical allocation-size panic, unreachable on a real machine (below) |

Nothing has to change before sign-off. There are two suggestions. One is a test-coverage gap; the other is a
cosmetic fix to a comment.

## 1. `snapEncC_ok`

`snapDecode (snapEnc c) = some c.model` when `ufWire` holds at both levels and `walSnapSize c < 2^63`.

**Consistency in Lean.** `snapDecode` is opaque. Only this axiom constrains it, plus the generic
`UnmarshalPb.spec`'s D1, through `wire` (enrolled by `pbSnapC_reg`). The axiom is inconsistent only if two
valid contents have equal `snapEnc` but different models. Each tag in `snapEnc c` can be parsed
deterministically:
- known fields come first, in number order;
- `ufWire` routes every unknown field away from the schema's (number, wire type) pairs;
- the ConfState's bytes sit inside one LEN field, and its unknown fields are routed the same way at `csSchema`.

So the decomposition is unique. In fact `snapEnc` is injective on valid contents, which D2 of `UnmarshalPb`
needs too: D2 makes the decoded `c` equal to *every* `c₀` encoding to the same bytes. Go's deterministic
decoder is a witness for both D1 and this axiom: `snapDecode := (Go decode).map model`.

**Faithfulness to Go.** The cited test (`examples/stdlib/walpb/snapshot_test.go`, `TestSnapshotEncoder`)
generates unknown fields with numbers 1..40, wire types 0/1/2/5 and minimal values only. The premise allows
more: groups nested up to 10001 deep, numbers up to 2^29-1 (including 19000-19999), non-minimal varint values
and non-minimal inner and end tags inside groups, and inner group numbers up to 2^31-1.
`hardstate_adv_test.go` covers this for HardState; nothing covered it for Snapshot.
`TestSnapshotEncoderAdversarialUF` (300,000 contents, all of the above at both levels, ufWire-checked by a
transcription of `UfWire.lean`) checks the following against `snapEnc`, and all pass:
- `proto.Size`;
- `proto.Marshal`;
- `MarshalOptions{}.MarshalAppend`;
- `proto.Unmarshal(snapEnc c)` giving exactly `c`;
- `proto.Clone`.

**Depth boundary.** `TestSnapshotDeepGroups`: a group chain 10001 deep decodes at both the Snapshot level and
the ConfState level; 10002 fails at both. The ConfState is one message deeper, but
`internal/impl/decode.go:220` parses unknown fields with `protowire.ConsumeFieldValue` and a fresh
`DefaultRecursionLimit`, so `WVal 10001` is exact at both levels.

**Attacks tried, all blocked:**
- index or term nil versus `some 0` (the model's `getD` agrees, and the encodings differ);
- ConfState nil versus empty (`some` empty encodes `1a 00`, which decodes back to a non-nil empty ConfState);
- `AutoLeave` true encoded as a non-1 varint (Go decodes it as true, but `snapEnc` only produces 0 or 1);
- a known field number with a wrong wire type in the unknown fields (Go routes it to unknown, and `Routed`
  allows it);
- packed LEN for the ConfState lists in the unknown fields (excluded, because `csSchema` declares `[0, 2]`);
- a group at field 3 (`consumeMessageInfo` returns `errUnknown`, and `Routed` allows it);
- numbers 0 or 2^29 (excluded by `TagOk`).

## 2. `pbSnapC_reg`, 3. `pbRecordC_reg`

**No conflicting registration.** `pbModelOf` (`Proof/google_golang_org/protobuf/proto/InvProto.lean:165`)
is opaque, and only `_reg` axioms constrain it. The tree has one registration each at `walpb.Snapshot.ty`
and `walpb.Record.ty`. These are `Named "go.etcd.io/etcd/server/v3/storage/wal/walpb.{Snapshot,Record}"`,
distinct from every other registered name (raftpb Message/Entry/HardState, the client/v3 types). The parts
`RaftNoAx` and `RaftTla` have their own `pbModelOf` and do not register walpb types.

Perennial has no protobuf model (the pin has no `protobuf` under `Perennial/`), so nothing conflicts with
Perennial's own proto model. The key is a Go type, not a location, so the cross-world check does not apply.
Function-valued `pbModelOf` with distinct keys is satisfiable.

**What a registration really claims.** It enrolls the instance in every generic spec quantified over
registered pairs:
- `UnmarshalPb` (D1 and D2);
- `SizePb`;
- `MarshalPb`;
- `MarshalAppendPb` (zero options);
- `ClonePb`;
- `pbutil.MustMarshalMessage`;
- `pbutil.MustUnmarshalMessagePb`.

I checked each of them at both instances.

- **D1 at Snapshot.** `TestSnapshotD1`: 1,000,000 adversarial inputs, 258,618 of which decode. The inputs
  include:
  - repeated and merged `conf_state` occurrences;
  - packed lists;
  - non-minimal tags and values;
  - wrong wire types;
  - mismatched groups;
  - numbers 0 and 2^29;
  - truncations.

  On every decode the unknown fields satisfy `ufWire` at both levels, the size is at most 2× the input, the
  re-marshal equals `snapEnc` of the decoded content, and decoding that gives the content back (D2).
- **The size bound at Snapshot.** The worst case is a packed list re-encoded unpacked, with ratio
  2k/(k+2+…) < 2. The outer length prefix does not break it: k = 64 re-encodes to 131 bytes from 68
  (131 ≤ 136).
- **Clone and Unmarshal keep presence.** Both keep the ConfState's presence and both levels' unknown fields.
  At Record they keep a non-nil empty `Data` (`TestRecordEmptyData`, encoding `1a00`). `RecC.data`'s
  `some []` therefore survives both, so `ClonePb`'s `c' = c` holds.
- **Marshal at Snapshot (zero options).** `proto/encode.go:174-210` runs `Size` (no cached-size flag, so
  nested sizes are recomputed and cached) before the marshal with `MarshalUseCachedSize`. The nested
  ConfState's prefix therefore uses a fresh cache. A frozen (`↦□`) ConfState shared with other messages
  always caches the same size. So the `SizeMismatchError` path (`internal/impl/codec_field.go:169`) is not
  reachable from these preconditions.
- **The decoded objects.** `snapOwnC` and `recOwnC` own the decoded objects whole. Go's decoded message is
  fresh, and `Data` is copied out.

**Caveat (a proof obligation, not a soundness issue).** `walCsHidden` and raft's `pbMsg raftpb.ConfState`
invariant are separate `inv (nroot.@"protobuf")` assertions over the same hidden cells, possibly at
different `uf`. That is not contradictory, because nothing can open both at once (they share a namespace).
The file header already records that at C6 they must be the same invariant.

## 4. `proto.MarshalAppendCachedRecord.wp_proof`

The spec says: `MarshalOptions{UseCachedSize: true}.MarshalAppend(b, rec)`, at the registered Record only,
appends `recEnc c`. The result is in place (same pointer, same capacity), or fresh with `b`'s array
returned at arbitrary contents.

**Against v1.36.12.** `MarshalAppend` (`proto/encode.go:153`) calls `marshal`. If
`cap(b) < len(b)+cachedSize`, it uses a fresh `make` and `copy` (:189-192). Then
`marshalAppendPointer` only appends. The only producer of a nested `SizeMismatchError` is
`appendMessageInfo`, and Record has no message field, so a stale cache cannot change the bytes. It changes
only whether the result is in place or fresh. Both cases are in the post's disjunction, and the fresh case
gives `b` back at `∃ ys`. `checkInitialized` passes (no required fields), so the error is always nil. The
literal `cachedSizeOpts = ⟨zero, false, false, true⟩` matches the field order
(NoUnkeyedLiterals, AllowPartial, Deterministic, UseCachedSize) in `GeneratedProof/.../proto.lean:52-55`.

**Aliasing.** The precondition's `b ↦* xs ∗ ownSliceCap b 1` (full fraction) separates `b`'s whole array
from:
- the record's `Data ↦*□` (only an empty `Data` can alias, and it reads nothing);
- the invariant's `unknownFields ↦* uf`.

**Test.** `TestRecordMarshalAppendCachedAdv`: 200,000 records with adversarial unknown fields (groups, large
numbers), the cache fresh, stale-small, stale-large or empty, and random `len`/`cap` of `b` (including 0).
In every run the bytes equal `xs ++ recEnc`. Every in-place result keeps `b`'s capacity. Every fresh result
shares nothing with `b`'s array, and `b`'s first `len b` bytes are unchanged. The same loop checks
`recEncC_ok`'s round trip at these unknown fields. The repository's `marshalappend_test.go` covers the
ownership claim on simple records.

**Caveat (theoretical).** The hidden-field invariant allows any `sizeCache`. With a stale cached size near
2^31 and `len(b)` near 2^47, `growcap` could request more than `maxAlloc` (2^48), and Go would panic
(`makeslice: cap out of range`). The precondition bounds only `xs.length + size < 2^47`, not the cached
value. Reaching this needs a 128 TiB buffer, so no program can exhibit it. If you want it closed on paper,
tighten the premise to `xs.length + size < 2^47 - 2^31`, or state it as `xs.length < 2^46`. The WAL calls
it with `e.buf[:0]` (1 MiB). Not needed for sign-off.

## Suggested changes (none blocking)

1. Adopt `TestSnapshotEncoderAdversarialUF`, `TestSnapshotDeepGroups` and `TestSnapshotD1` (and the
   adversarial Record round trip) into `examples/stdlib/walpb/`, as `hardstate_adv_test.go` was for
   HardState. `snapEncC_ok`'s docstring cites only `TestSnapshotEncoder`, whose generator does not cover
   the premise (no groups, numbers ≤ 40, minimal values). The same holds for `record_test.go`'s `genUF`,
   which `recEncC_ok` cites.
2. Cosmetic: `examples/stdlib/walpb/marshalappend_test.go`'s header names the spec at
   `LinuxFs/Spec/...`, a path from before the 2026-11-15 move. It is now
   `Spec/google_golang_org/protobuf/proto/MarshalAppendCachedRecord.lean`.

## Not tried

- Lean-side counterexample proofs (no build allowed). No Go-side gap was found to warrant one.
- Inputs above 2 GiB: the int32 size cache's zero path, and `Unmarshal` at that size.
- Concurrent `Marshal` of a Snapshot whose ConfState is shared with a concurrently sized raft message.
  Argued safe from frozen content (same size written atomically), not run.


---

# Axiom review: `fmt.SprintfWalName.wp_proof`, `fmt.SscanfWalName.wp_proof` (2026-11-21)

Checkout reviewed: `/shared/etcd-grove-walns` (branch `wal-nostorageok`, `24829ac036`), Perennial pin
`5dab16ec22dd9f2974dd2df3216cd0f28d48c344` (`lake-manifest.json`; fetched into the shared Perennial
clone's object store to read it). Go: `go1.27.3 linux/amd64` (the `GO_TOOLCHAIN` of `etc/goose.py`).
No build was run (as instructed); everything below is from the source text and Go programs.

**Update 2026-11-24.** `fmt.SprintfWalName.wp_proof` is no longer an axiom: the real-`fmt` pin bump (Perennial
`52d62e83c`, lean `af4fd74b00`) proved it over the corrected `Sprintf` model, so the finding below is resolved.
Go programs: the review's scratch (not kept in the repository) (`model_test.go`: the Lean model transcribed,
copied from `examples/stdlib/fmtwalname`; `extra_test.go`: new tests; `out.txt`: the output).

| Axiom | Verdict |
|---|---|
| `fmt.SprintfWalName.wp_proof` | **True of Go, false of the model it is stated over.** It contradicts Perennial's trusted model of `Sprintf`. `fmt.Assumptions.Sprintf_unfold` fixes that model, and the axiom itself assumes `fmt.Assumptions`. So every closed theorem that rests on the axiom is, as a Lean statement, false of the operational semantics it names. With adequacy and an explicit model execution this gives `False` (not mechanized here). Must change before sign-off. |
| `fmt.SscanfWalName.wp_proof` | **Sound with caveats.** It matches Go 1.27.3's `fmt/scan.go` on every input tested, and the code reading agrees. The only caveat is the general one for names-only axioms: the axiom quantifies over every function table. |

The two axioms do not interact unsoundly. The only thing that links them is the round trip
`fmt.scanWalName_walNameStr`, a proved pure lemma. The other `Sscanf` axiom, `fmt.Sscanf.spec`
(`"%d"`, one `*int`), is about a different format literal, so no call matches both.

---

## 1. `fmt.SprintfWalName.wp_proof`

### Claim
`Sprintf("%016x-%016x.wal", s, i)` called with `[uint64 s, uint64 i]` as `any`s returns
`fmt.walNameStr s i`. Both numbers are written as 16 lowercase hex digits, zero-padded. The args
slice is returned. The only premise is `isPkgInit fmt`. Section variables:
`[package_sem : fmt.Assumptions]`.

### Against Go: true
- `fmt/print.go` → `fmtInteger` with the `zero` flag pads to the width after the sign. A `uint64` has
  no sign, and its value is below 16^16, so the result has exactly 16 digits. The digits are
  lowercase for `x`.
- Measured: 1,000,000 random pairs (random bit lengths), plus `0`, `2^63`, `2^63-1` and `2^64-1`.
  The output always equals the Lean `walNameStr` transcription, and its length is always 37.
  `examples/stdlib/fmtwalname` already checks 100,000 pairs and the edge values.

### Against Perennial's model: false
- `Perennial/Code/fmt.lean` (at the pin) contains `class fmt.Assumptions … Sprintf_unfold : FuncUnfold Sprintf [] Sprintf.impl`.
  So in every instance the axiom quantifies over, `@! fmt.Sprintf` runs the trusted model
  `Perennial/TrustedCode/fmt.lean`.
- In the model, `doPrintf` reaches `%016x` at `i = 0` with `out = ""`.
  - `formatArg` accepts only plain `%x` (`format[i+1] == 'x'`).
  - `intVerb` accepts a width only before `d` (line 76: `format[j] == 'd'`), so `%016x` is not formatted.
  - `doPrintf` therefore returns `out + arbitraryString()`.
  - `arbitraryString` loops `for arbitrary() != 0`.
  - `ArbitraryInt` is a real nondeterministic step: `BaseStep.ArbitraryIntS (x : w64)` for every
    `x` (`GooseLang/Lang.lean:897`).
- So the model has an execution that returns `""`. It also has executions returning every other
  string.
- Perennial says this is intended: `SprintfOut` is documented as "`out` is a *possible* result of the
  model". The model does not leave the output unspecified. It specifies it as nondeterministic.
- The axiom says every execution returns `walNameStr s i`. That is false in every instance satisfying
  `fmt.Assumptions`.
- This differs from the known caveat for names-only axioms (`notes/status-history.md`: "Axioms like
  `reflect.DeepEqual.wp_proof` quantify over every semantics instance… consistent only as long as no
  such model is built"). For `Sprintf` the contradicting model is already built and fixed by the
  axiom's own premise class. The hypothesis-class fix used for names-only axioms (`DialWithBalancerBody`, `log.NewModel`) does not help here.
- None of the repository's other `Sprintf`/`Errorf` axioms narrows the model's output
  (`SprintfSlice`, `SprintfClientPtr` and `ErrorfStrs` post `SprintfOut` or nothing). This axiom is
  the only one that does.

### The counterexample (model-level, not a Go panic)
```go
package axiomcx
import "fmt"
func Main() {
	if fmt.Sprintf("%016x-%016x.wal", uint64(0), uint64(0)) != "0000000000000000-0000000000000000.wal" {
		panic("model")
	}
}
```
- **In Go:** it never panics, so this is not a counterexample in the skill's strict sense.
- **With the axiom:** `wp_apply fmt.SprintfWalName.wp_proof`, then `fmt.walNameStr 0 0 =
  go!"0000…wal"` by `decide`. That proves `{{ isPkgInit … }} Main {{ True }}`, and adequacy gives "no
  execution of `Main` in the model panics".
- **In the model:** the first `ArbitraryInt` in `arbitraryString` returns 0, the call returns `""`,
  and `Main` panics.
- **Deriving `False`:** this needs that execution as a Lean term (stepping `doPrintf`/`visitRest`
  for one directive). That is finite and definitional, but laborious. I did not build it, and no build
  was allowed. Inside the program logic there is no contradiction: Iris has no rule that combines
  two WPs of one expression, and `SprintfOut` admits `walNameStr`. The inconsistency is
  between the axiom and the adequacy theorem.

### What it rests on
`etc/tcb-baseline.txt:169`, and the collections `wal-fsext`, `wal-tester`, `leaseexpiryN` and `etcd-all`. The axiom is used
by `WAL.cut`, `Create`, `openAtIndex`, `ReadAll` and the WAL `Link.lean`. Every closed result over
the WAL (and the results over the server that reach it through `leaseexpiryN`/`etcd-all`) is, as a
Lean statement about the model, false only for this reason. Its Go meaning is unaffected.

### Suggested change (must be decided before sign-off)
1. **The real fix:** Perennial change (1) of `notes/perennial-changes.md`, "`Sprintf`'s `%0Nx`":
   `intVerb` accepts `%0Nx`, and `formatHex` pads with zeros after the sign. Then the axiom becomes a
   corollary of `fmt.Sprintf.wp_proof`, where `SprintfOut` for this format determines the output.
   Status at the pin and at Perennial `origin/lean` (`ddc0f0acc`): not landed (`intVerb` still
   checks only `'d'`). This is a general Perennial change, not one shaped by this proof, so it fits
   CLAUDE.md's rule.
2. **Until then:** the axiom cannot be made consistent locally. Any statement that pins the
   output contradicts `Sprintf_unfold`. If the user accepts it as an interim trust assumption,
   record it as what it is:
   - an `audit.md` row: "false of Perennial's model, true of Go; inconsistent with `fmt.Assumptions`
     via adequacy; pending the `%0Nx` model change";
   - the docstrings in `Spec/fmt/SprintfWalName.lean` and `Proof/fmt/SprintfWalName.lean` say "beyond
     Perennial's model … its output is arbitrary". That understates it: the model does not leave the
     output open, it makes every string a possible outcome, and the axiom narrows that. The docstrings
     should say "contrary to".
3. Smaller: `notes/perennial-changes.md`'s workaround text calls the axiom "beyond the model". Update
   it the same way.

---

## 2. `fmt.SscanfWalName.wp_proof`

### Claim
`Sscanf(str, "%016x-%016x.wal", &seq, &index)` takes the args `[*uint64 p, *uint64 q]`, full
`p ↦ a0 ∗ q ↦ b0` (separate, so `p ≠ q`) and `isPkgInit fmt`. It returns the slice and
`p ↦ a ∗ q ↦ b` for some `a b`:
- if `scanWalName str = .ok x y`, then `err = nil`, `a = x` and `b = y`;
- if it is `.err`, then `err ≠ nil`;
- if it is `.unknown`, nothing is claimed.

`cnt` is unconstrained. `fmt.Sscanf` is names-only at the pin: `Code/fmt.toml` neither translates
nor trusts it, and `fmt.Assumptions` has no `Sscanf_unfold`. So no Perennial model contradicts the
axiom.

### Code reading (go1.27.3 `src/fmt/scan.go`)
- **`doScanf` (1181):** `parsenum` reads `016` as width 16, because scanf has no flags. It calls
  `SkipSpace` before the verb, then sets `argLimit = count + 16`, which bounds the token in runes. It
  then calls `scanOne` → `case *uint64` → `scanUint('x', 64)`.
- **`scanUint` (671):** `SkipSpace`, then `notEOF` (`panic(io.EOF)`, which `errorHandler` turns into
  `err = io.EOF`). There is no sign: `scanInt` accepts one, `scanUint` does not, so `+` and `-` give
  "expected integer". Then `getBase('x')` gives `hexadecimalDigits` (both cases), and `scanNumber`
  needs at least one digit. 16 digits always fit in `ParseUint(…, 16, 64)`, so there is no overflow
  path.
- **`*v` is stored after the token is parsed.** So a later failure (`-`/`.wal` mismatch, the second
  number) leaves `seq` written. The spec allows this: `a`, `b` are arbitrary in `.err`/`.unknown`.
- **Literals go through `advance` (1100):** `mustReadRune` (EOF → `ErrUnexpectedEOF`), and a mismatch
  returns -1 → "input does not match format". A 17th hex digit is compared with `-` or `.` and fails.
  This matches `scanHex16`'s `16 < length → none`.
- **Trailing input is never checked** (`Fscanf` does not require EOF), so `.walx`, `.wal.tmp` and
  `.wal\n` are `ok`. This matches the model (`<+:`).
- **Spaces:** `SkipSpace` (Unicode spaces; a newline is an error for `Sscanf`) appears only at the two
  verb starts. The model gives `.unknown` at every byte that may begin a space there (`\t..\r`,
  `' '`, `≥ 0x80`). That is conservative and correct.

### Tests (go1.27.3, `extra_test.go`, all pass)
- **40 edge inputs**, each compared with the transcribed `scanWalName`; outcomes in `out.txt`:
  - `""`, `"1"`, `"1-"`, `"1-2"`, `"1-2.wa"`: error (`EOF`/`unexpected EOF`); model `.err`.
  - `"1-2.WAL"`: mismatch; model `.err`.
  - `"+1-2.wal"`, `"1-+2.wal"`, `"-1-2.wal"`: "expected integer"; model `.err`.
  - `"0x1-2.wal"`: `seq=0` written, then error; model `.err`.
  - 17 digits, in either number: error; model `.err`.
  - Uppercase `ABCDEF-abcdef.wal` and `FFFFFFFFFFFFFFFF-…`: `ok`; model `ok`, same values.
  - Values ≥ 2^63: `ok`.
  - Invalid UTF-8 or NBSP inside the name: error; model `.err`.
  - NBSP, `\n`, `\r\n` and `\xff` at a number start: model `.unknown` (Go returns either `nil` or an
    error there; both are allowed).
  - `"1-2.wal\x00"` and `"1-2.wal\n"`: `ok`.
- **1,000,000 random strings** mixing WAL-ish pieces with **arbitrary bytes 0–255**. The existing
  `examples/stdlib/fmtwalname` alphabet has none of these bytes. Outcomes: 642 `ok`, 821,432 `err`,
  177,926 `unknown`; no mismatch.

### Ownership and init
- **Reads only.** `Sscanf` only reads the args slice: `dq` is fine and the slice is returned. It does
  not keep the slice or the pointers (`ss` goes back to `ssFree`, and `free` clears `buf`).
- **Writes.** It writes only `*p` and `*q`, both owned.
- **`isPkgInit fmt`** is a premise only. It cannot make the spec unsound.
- **Concurrency.** Concurrent calls are safe: `sync.Pool`.

### Caveats (not defects)
- **The general caveat for names-only axioms.** The axiom holds for every `GoSemanticsFunctions`, so a
  constructed function table with `functions "fmt.Sscanf" = panic` would refute it
  (`notes/status-history.md`'s caveat, which applies to every `*.wp_proof` axiom).
- **When Perennial gets a model of `Sscanf`** (proposed change (2)), replace this axiom by a proof.
  If that model over-approximates (arbitrary results past a byte that may begin a space), check the
  `.unknown` case matches it. Otherwise this axiom would fall into the `Sprintf` trap of §1.
- **`Sscanf` accepts names the WAL never writes**, as the header of `Proof/fmt/WalName.lean` says:
  `"1-2.wal"`, uppercase, `"0-0.wal.wal"`, and with leading spaces (`.unknown`). This is Go's real
  behaviour, so it is not a soundness issue. The WAL's proofs do not rely on such names being
  rejected, because they use the directory invariant that every `.wal` name is a `walNameStr`
  (`selectWALFiles`, `searchIndex`, `isValidSeq` premises). That invariant is the WAL's premise,
  outside these axioms.

### Suggested change
None required. Optionally, add an `audit.md` row: "ok (matches go1.27.3 `doScanf`/`scanUint` on this
format; 1M random byte strings), with the general names-only caveat". Neither axiom has an
`audit.md` row today.
