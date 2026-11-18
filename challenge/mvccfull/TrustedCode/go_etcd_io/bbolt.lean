/-
Trusted Go model of bbolt's `splitThreshold` (`node.go`, the fork's branch `goose-lean-v2`), in
namespace `go_etcd_io.bbolt` like the generated package (`Code/go_etcd_io/bbolt.toml`: `trusted =
["splitThreshold"]`; decision D17 of the bbolt spec, `notes/bbolt-v2-infra.md`). linux/amd64.

```go
func splitThreshold(pageSize uintptr, fillPercent float64) int {
	if fillPercent < minFillPercent {      // 0.1
		fillPercent = minFillPercent
	} else if fillPercent > maxFillPercent { // 1.0
		fillPercent = maxFillPercent
	}
	return int(float64(pageSize) * fillPercent)
}
```

`node.splitTwo`'s threshold, factored out of it unchanged by the fork. Perennial gives this code no
meaning that bounds its result: float multiplication and comparison are uninterpreted
(`float64Mul`, `float64Leb`), and a float-to-int conversion is an `ArbitraryInt`
(`convert_float64_to_integer`). Translated, the threshold would be any `int`, and `node.write`'s
`inode overflow` panic would be reachable in the model though not in Go. The model states the
bounds Go's computation has instead.

**The model.** It picks an arbitrary `int` `t` and returns it if `splitThresholdOk pageSize fp t`
holds, and otherwise never returns (an infinite loop):

* `fp` is a NaN (the bits of a `float64` are the value's representation here, so the test is
  on them: exponent all ones, fraction non-zero), or
* `2^53 ≤ pageSize`, or
* `0 ≤ t ≤ pageSize` (`t` as a signed `int`, `pageSize` as an unsigned `uintptr`).

**Faithfulness: every result Go returns is one the model may return.** The model only ever adds
behaviours to Go's: `ArbitraryInt` can pick Go's result, so it suffices that Go's result passes
the test whenever the first two disjuncts fail; non-termination is a behaviour no safety proof
can use. Suppose `fp` is not a NaN and `pageSize < 2^53`.
- The clamp makes `fp ∈ [0.1, 1.0]`: a finite `fp` below `0.1` (including `-Inf`) becomes `0.1`,
  above `1.0` (including `+Inf`) becomes `1.0`; a NaN would pass both tests, but it is excluded.
- `float64(pageSize)` is exact, since `pageSize < 2^53` is representable.
- The product `x · fp` of an exact `x ≥ 0` and `fp ∈ (0, 1]`, correctly rounded, lies in
  `[0, x]`: the exact product is in `[0, x]`, and rounding to nearest is monotone and fixes the
  representable bounds `0` and `x`.
- `int(...)` truncates a finite value toward zero; a value in `[0, x]` with `x < 2^53 < 2^63` is
  in range, so the result `t` satisfies `0 ≤ t ≤ pageSize`.
For a NaN `fp` Go's result is platform-dependent (`MinInt64` on amd64, `0` on arm64), and for
`2^53 ≤ pageSize` `float64(pageSize)` may round up and a product of `2^63` or more converts to
`MinInt64` on amd64; the model returns any `int` in both cases. bbolt's page size is the OS's
(4096) or the file's meta's, far below `2^53`.

`rebalance`'s own threshold (`node.go`, `int(float64(pageSize)*FillPercent) / 2`, unclamped) is
left translated, so arbitrary: its early return also needs `len(n.inodes) > n.minKeys()`, so
empty nodes and one-child branches are rebalanced whatever the threshold, and a different
threshold only changes how much is merged, which `spill` re-splits.
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace go_etcd_io.bbolt
section code
variable [GooseExts] [GoGlobalContext]

/-- `splitThreshold(pageSize, fillPercent)`: some `int` within Go's bounds (see the file header);
the test `splitThresholdOk` in code, then the arbitrary result or divergence. -/
noncomputable def splitThreshold.impl : val :=
  λ: "pageSize" "fp",
    let: "t" := ArbitraryInt in
    let: "nan" :=
      if: ("fp" &⟨go.uint64⟩ #(W64 0x7FF0000000000000)) =⟨go.uint64⟩ #(W64 0x7FF0000000000000)
      then ("fp" &⟨go.uint64⟩ #(W64 0x000FFFFFFFFFFFFF)) ≠⟨go.uint64⟩ #(W64 0)
      else #false in
    let: "ok" :=
      if: "nan" then #true
      else if: #(W64 (2 ^ 53)) ≤⟨go.uintptr⟩ "pageSize" then #true
      else if: #(W64 0) ≤⟨go.int⟩ "t" then "t" ≤⟨go.uint64⟩ "pageSize"
      else #false in
    if: "ok" then "t"
    else (rec: "diverge" <> := "diverge" #()) #()

end code
end go_etcd_io.bbolt

end Perennial
