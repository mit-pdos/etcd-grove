# `auth.tokenSimple.genTokenPrefix.wp_proof`

**Reviewed** 2026-10-31 by the `axiom` skill, branch `axiom/gentokenprefix` off `auth-a4`
(`fa87a843c8`). **Verdict: survives** every attack tried; no counterexample program.

## The axiom

`Proof/go_etcd_io/etcd/server/v3/auth/tokenSimple__genTokenPrefix.lean` (C1's A4), triple
`Spec/go_etcd_io/etcd/server/v3/auth/tokenSimple__genTokenPrefix.lean`: for every `p : Loc`,

    {{ isPkgInit auth }} p.genTokenPrefix() {{ (s, err). ⌜err = nil ∧ tokPrefixOk s⌝ }}

with `tokPrefixOk pre := W8 32 ∉ pre` (`Proof/go_etcd_io/etcd/server/v3/auth/Model.lean:134`).
Claims: (1) no panic, for any receiver, nil included; (2) the error is `nil`; (3) the string has
no space byte. It consumes and returns no resources (the receiver is not owned).

## The Go code at the pin

etcd fork `249d76bea7`, `server/auth/simple_token.go:110-123`:

    ret := make([]byte, 16)
    for i := 0; i < 16; i++ {
        bInt, err := rand.Int(rand.Reader, big.NewInt(int64(len(letters))))
        if err != nil { return "", err }
        ret[i] = letters[bInt.Int64()]
    }
    return string(ret), nil

`letters` (`:35`) is `[a-zA-Z]`, 52 bytes. The receiver `t` is never read.

Go go1.27.3 (`GO_TOOLCHAIN` of `etc/goose.py`):

- `crypto/rand.Int` (`crypto/rand/util.go`): panics only on `max.Sign() <= 0` (here `max = 52`);
  its only error is `io.ReadFull(rand, bytes)`'s; its result is `< max` (rejection loop,
  `n.Cmp(max) < 0`), and `≥ 0` (`SetBytes`). So `letters[bInt.Int64()]` is in range.
- `crypto/rand.Reader` (`crypto/rand/rand.go:34`) is `crypto/internal/rand.Reader`, `reader{}`
  (`crypto/internal/rand/rand.go:19-31`), whose `Read` always returns `len(b), nil`: without
  boringcrypto it calls `drbg.Read`, which has no error result (`sysrand.Read` crashes the
  program via `runtime.fatal` when the OS fails; in FIPS mode the DRBG is reseeded, no error);
  with boringcrypto a failed `boring.RandReader.Read` panics.

## Attacks tried

1. **A non-nil error** (false pure fact `err = nil`), from the default reader: impossible at the
   pin, the default `reader.Read` never returns an error (above). Go test: 200 000 calls, no
   error (below).
2. **An error from a reassigned `crypto/rand.Reader`** (the docstring's margin). Real in Go:
   the test below sets `rand.Reader = errReader{}` and gets `err = bad reader`. Blocked in the
   model: the counterexample program would have to store to `crypto/rand.Reader`, and Perennial's
   `crypto/rand` (`Perennial/TrustedCode/crypto/rand.lean`, `Proof/crypto/rand/Base.lean:32`)
   gives only `globalAddr Reader ↦□ rdr` after initialization, so no proof can perform the store.
   The modelled world has no reassignment; this axiom's claim is true there. (Whether Perennial's
   `↦□` of a Go-assignable exported variable is the right model is Perennial's question: it is
   sound, since it only makes the write unprovable, but a program that assigns `rand.Reader` has
   no proof.) etcd's non-test code never assigns it (`grep -rn 'rand.Reader *='` over the fork:
   nothing).
3. **A space (or any non-letter) in the prefix**: every byte is `letters[k]` with `0 ≤ k < 52`;
   none is 32. Go test checks every byte of 200 000 prefixes.
4. **A nil or zero receiver**: `t` is never dereferenced; the test calls it on
   `(*tokenSimple)(nil)` and `&tokenSimple{}`, no panic.
5. **Index out of range / `Int` panic**: `max = 52 > 0`; result `< 52`.
6. **Concurrency**: no shared state of etcd's; `crypto/rand.Reader` is documented safe for
   concurrent use (the DRBG's instances are pooled, `drbg.Read`).
7. **GODEBUG / FIPS**: `GODEBUG=fips140=on` run of the claims test passes; `cryptocustomrand`
   only affects `CustomReader`, which `rand.Int` does not call.

## Not tried

- **boringcrypto builds** (`GOEXPERIMENT=boringcrypto`): `reader.Read` panics when BoringSSL's
  RNG fails, an environment failure no test can drive; the same class as the OS RNG failure
  (a crash outside the model). Not the default build.
- No Lean counterexample (none to build). No `lake build` was needed (nothing in Lean changed).

## The Go test

Run in a scratch copy of the pinned fork (`server/auth/axiom_gtp_test.go`, an internal test, since
`genTokenPrefix` is unexported), `GOTOOLCHAIN=go1.27.3 go test -count=1 -v -run
TestAxiomGenTokenPrefix ./auth/`:

```go
func TestAxiomGenTokenPrefixClaims(t *testing.T) {
	var nilT *tokenSimple
	zero := &tokenSimple{}
	for i := 0; i < 200000; i++ {
		r := nilT
		if i%2 == 1 { r = zero }
		s, err := r.genTokenPrefix()
		if err != nil { panic("claim: err != nil: " + err.Error()) }
		if strings.IndexByte(s, ' ') >= 0 { panic("claim: space in prefix") }
		for j := 0; j < len(s); j++ {
			if !strings.ContainsRune(letters, rune(s[j])) { panic("non-letter") }
		}
	}
}

type errReader struct{}
func (errReader) Read([]byte) (int, error) { return 0, errors.New("bad reader") }

func TestAxiomGenTokenPrefixReassignedReader(t *testing.T) {
	old := rand.Reader
	rand.Reader = errReader{}
	defer func() { rand.Reader = old }()
	_, err := (*tokenSimple)(nil).genTokenPrefix()
	t.Logf("with rand.Reader reassigned: err = %v", err)
}
```

Output:

    === RUN   TestAxiomGenTokenPrefixClaims
    --- PASS: TestAxiomGenTokenPrefixClaims (0.37s)
    === RUN   TestAxiomGenTokenPrefixReassignedReader
        axiom_gtp_test.go:45: with rand.Reader reassigned: err = bad reader
    --- PASS: TestAxiomGenTokenPrefixReassignedReader (0.00s)
    PASS

(and `GODEBUG=fips140=on`: `ok go.etcd.io/etcd/server/v3/auth`).

## Note on the docstring

Accurate. One precision: with boringcrypto a failed read *panics* (`crypto/internal/rand/rand.go:23`),
a recoverable panic rather than a crash; like the OS-failure crash it is an environment failure
outside the model, so the verdict stands.
