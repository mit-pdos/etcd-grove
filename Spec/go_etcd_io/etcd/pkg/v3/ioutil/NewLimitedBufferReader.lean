/-
## `ioutil.NewLimitedBufferReader(r, n)`

**Users.** `pipelineHandler.ServeHTTP` (`rafthttp/http.go:121`: the request body, `n =
connReadLimitByte`, 64 KiB), read by `io.ReadAll`. Snippet: `examples/specreq/pkgleaves/leaves.go` (`ReqLimitedRead`).

**Proof sketch.** Allocates `&limitedBufferReader{r, n}`. Its `Read(p)` (translated) slices `p` to
`n` (in bounds for `0 ≤ n`: `np[:n]` panics at a negative `n`) and calls `r.Read` on the prefix
(`Http.readerAt_read.spec`): the bytes land in `p`'s prefix (the sub-slice aliases it), so each call
is a `Read` of `r` with the same knowledge; hence the returned reader has `r`'s contract.

**Changes.** From `specs-ref`'s `NewLimitedBufferReader.lean` (`prefixReaderOk`, `0 < n`): over
2f's `readerAt`; `0 ≤ n` (a zero cap reads nothing but does not panic).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.ioutil.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace IoUtil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **A reader with `r`'s contract**, each `Read` capped at `n` bytes. -/
def NewLimitedBufferReader.spec : Prop :=
  ∀ (r : GoInterface) (Pre Φ : List w8 → IProp GF) (bs : List w8) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil ∗ Http.readerAt r Pre Φ bs ∗
      ⌜0 ≤ sint.Z n⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.ioutil.NewLimitedBufferReader)) (Val #r)) (Val #n))
  {{ (r' : GoInterface), RET #r'; Http.readerAt r' Pre Φ bs }}

end spec
end IoUtil
end EtcdGrove
end Perennial
