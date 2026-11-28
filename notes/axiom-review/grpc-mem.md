# Review: grpc's `mem` translated; `grpc.CustomCodec.wp_proof` proved (2026-11-26, grpc-mem)

**Target.** Branch `grpc-mem/2026-11-26`. It retires the axiom `grpc.CustomCodec.wp_proof`.
`CustomCodec`'s closure, `o.codec = newCodecV0Bridge(c)`, converts `codecV0Bridge{codec: c}` to
`baseCodec`. That type used to be axiomatized because its methods name `mem.BufferSlice` and grpc did
not import `mem`, so the semantics had no step for the conversion (`convert_to_interface` needs
`baseCodec.ty ≤u InterfaceType _`). Now grpc imports `mem` and `baseCodec` is a translated interface.

## The model change (trusted text: `models/grpc`, pre-approved under RULES #16: no axiom, no premise)

When grpc imports `mem`, `mem`'s initializer runs as part of grpc's. That initializer is
`init` → `NewBinaryTieredBufferPool` → `internal/mem.newBinaryTiered`, which calls `slices.Compact`.
goose refuses `slices.Compact`. Its `s[k] = s2[k2]` copies a type-parameter value between two memory
places (modelcheck R4). The model replaces that one call by a plain loop on `[]uint8`. The exact diff:

```diff
diff --git a/models/grpc/internal/mem/buffer_pool.go b/models/grpc/internal/mem/buffer_pool.go
index 00aeca419f..4a151cdf94 100644
--- a/models/grpc/internal/mem/buffer_pool.go
+++ b/models/grpc/internal/mem/buffer_pool.go
@@ -99,9 +99,31 @@ func NewDirtyBinaryTieredBufferPool(powerOfTwoExponents ...uint8) (*BinaryTiered
 	}, NewDirtySimplePool(), powerOfTwoExponents...)
 }
 
+// MODEL: compactExponents(s) is slices.Compact(s) on a []uint8, as a plain loop (goose refuses
+// Compact's generic element copy `s[k] = s2[k2]`, modelcheck R4): it returns the same slice (s[:k],
+// consecutive duplicates removed) and leaves s's array as Compact does (the elements after the
+// result zeroed). model_compact_test.go checks both against slices.Compact on random inputs.
+func compactExponents(s []uint8) []uint8 {
+	if len(s) < 2 {
+		return s
+	}
+	k := 1
+	for i := 1; i < len(s); i++ {
+		if s[i] != s[k-1] {
+			v := s[i]
+			s[k] = v
+			k++
+		}
+	}
+	for j := k; j < len(s); j++ {
+		s[j] = 0
+	}
+	return s[:k]
+}
+
 func newBinaryTiered(sizedPoolFactory func(int) bufferPool, fallbackPool bufferPool, powerOfTwoExponents ...uint8) (*BinaryTieredBufferPool, error) {
 	slices.Sort(powerOfTwoExponents)
-	powerOfTwoExponents = slices.Compact(powerOfTwoExponents)
+	powerOfTwoExponents = compactExponents(powerOfTwoExponents) // MODEL: slices.Compact, as a loop
 
 	// Determine the maximum exponent we need to support. This depends on the
 	// word size (32-bit vs 64-bit).
diff --git a/models/internal/grpcdifftest/run.sh b/models/internal/grpcdifftest/run.sh
index b9248c4c17..54e2420161 100755
--- a/models/internal/grpcdifftest/run.sh
+++ b/models/internal/grpcdifftest/run.sh
@@ -23,6 +23,8 @@ go test -count=1 "$@" ./...
 echo "== the model (models/grpc)"
 "$GM" "$D" vet -tags grpcmodel ./...
 "$GM" "$D" test -count=1 -tags grpcmodel "$@" ./...
+echo "== the model's rewrites against the library (models/grpc, in-package tests)"
+(cd "$ROOT/models/grpc" && go test -count=1 ./internal/mem/)
 echo "== the model, its choices random (the invariants)"
 GRPC_MODEL_CHOOSE=random "$GM" "$D" test -count=3 -tags grpcmodel -run 'TestAtMostOnce' "$@" ./
 echo "== examples/ against the model"
```

**The model's trusted claim is unchanged.** It is still "every behavior of grpc-go v1.84.0 over Linux
TCP, as the program observes it, is one of the model's" (`models/README.md`, the grpc row).

`compactExponents(s)` is `slices.Compact(s)` (go1.27.3) on every `[]uint8`:
- it returns the same slice header (`s[:k]`, consecutive duplicates removed);
- it leaves `s`'s whole array, capacity included, as `Compact` does: the elements after the result are
  zeroed (`clear(s[k:])`), and when `Compact` finds no duplicate it writes nothing;
- the loop writes `s[k] = s[k]` there, which leaves the same values, and nothing else runs concurrently
  on that array.

Evidence:
- `models/grpc/internal/mem/model_compact_test.go`, `TestCompactExponentsIsCompact`: 200,000 random
  inputs (lengths 0 to 40, capacity slack 0 to 3, sorted and unsorted, value spans 1 to 256). It
  compares the result's length, capacity and elements, and the whole array afterwards, against
  `slices.Compact` on a copy.
- The test fails when the tail zeroing is removed (checked by hand).
- `models/internal/grpcdifftest/run.sh` runs it.

## What is translated (`Code/google_golang_org/grpc/{mem,internal/mem}.toml`)

- `mem`: types only, plus its initializer's code:
  - `init` (`buffer_pool.go:52`);
  - `NewBinaryTieredBufferPool`;
  - the variables `defaultBufferPoolSizeExponents`, `defaultBufferPool` and `bufferObjectPool` (a
    `sync.Pool` literal);
  - the two interface-check blanks are goose `[[skip]]`s with the existing reason.
- `internal/mem`: types only, plus:
  - `init`;
  - `BufferPoolingThreshold` and `uintSize`;
  - `NewBinaryTieredBufferPool`, `newBinaryTiered`, `compactExponents` and `newSizedBufferPool`.
- grpc: `CustomCodec` and `newCodecV0Bridge` are translated with their bodies; `mem` is added to its
  imports.
- `internal`: its hook variables `SetDefaultBufferPool` and `SetBufferPoolingThresholdForTesting` are
  translated (allocations only).

## Proofs (untrusted)

- `internal/mem`:
  - `compactExponents`: the result is a prefix whose elements are the input's.
  - `newSizedBufferPool`.
  - `newBinaryTiered`:
    - The exponents are sorted (Perennial's `slices.wp_Sort_uint8`) and compacted, and each stays at
      most `62`, so the `fmt.Errorf` branch is not taken.
    - The two 63-entry tables come from Perennial's `slices.wp_Repeat` (`uintSize - 2 + 1`), and both
      the main loop and the two gap-filling loops index them in range.
  - `NewBinaryTieredBufferPool`.
- `mem.NewBinaryTieredBufferPool`.
- The generated initializers, with no `initFuncsOk` or `opaqueInitsOk`:
  - `internal/mem`'s fact `internalMemInit` (`cache/v3/Base.lean`) is `uintSize ↦□ 64`; no translated
    code writes `uintSize`.
  - `mem`'s fact is `True`.
  - Both `init`s store their closures in `internal`'s hook cells (`hookCell`, through `hooksAny`).
- `grpc.CustomCodec.wp_proof` is proved over the body against `srvOptFnOk .neutral`, using
  `srvCodecOk`'s second disjunct (`grpcProtoCodec c`). Its spec text is unchanged.
- Trust base: one axiom fewer. No axiom, premise or opaque is added, and no top-level statement changes.
