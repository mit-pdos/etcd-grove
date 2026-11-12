/-
# `pkg/v3/ioutil`: readers (batch 4b)

rafthttp reads a pipeline request's body through `NewLimitedBufferReader` (each `Read` capped) and
sends a snapshot's body as a `ReaderAndCloser` (a reader and a closer in one struct). Both are
stated in the HTTP boundary's reader vocabulary (2f's `Http.readerAt`, `Http.readerCloser`): a
reader built over a reader keeps its contract. No vocabulary of its own.

Users: `rafthttp/http.go:121` (`pipelineHandler.ServeHTTP`), `rafthttp/snapshot_sender.go:195`
(`createSnapBody`). Snippets: `examples/specreq/pkgleaves/leaves.go` (`ReqLimitedRead`,
`ReqReaderAndCloser`).

Left out: `NewExactReadCloser` (its one user, `snap.NewMessage`, is trusted as a whole, 2e),
`WriteAndSyncFile`, `PageWriter` (not translated, no translated user).

## Laws

`ReaderAndCloser_reader`, `ReaderAndCloser_closer` (below): the struct's promoted `Read` and `Close`
are its fields' (`ReaderAndCloser.Read`/`Close` call `rc.Reader.Read`/`rc.Closer.Close`); their proof
is 2f's intro law for a wrapper whose `Read`/`Close` is its field's (`Http.readerAt_wrap`,
`readerCloser_wrap`, requested in `req/net_http.md`): nothing outside 2f can make a `readerAt`.
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.ioutil
public import SpecPlan.Spec.PkgInit.go_etcd_io.etcd.pkg.v3.ioutil
public import SpecPlan.Spec.net.http.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace IoUtil

open Iris Iris.BI

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- The `io.ReadCloser` value of a `*ReaderAndCloser`. -/
def rcVal (l : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.ioutil.ReaderAndCloser.ty) #l

/-- **A `ReaderAndCloser` reads as its reader** (its `Read` is the reader's). -/
def ReaderAndCloser_reader.spec : Prop :=
  ∀ (l : Loc) (v : go_etcd_io.etcd.pkg.v3.ioutil.ReaderAndCloser) (Pre Φ : List w8 → IProp GF)
    (r : List w8),
  (l ↦□ v : IProp GF) ∗ Http.readerAt v.Reader' Pre Φ r ⊢ Http.readerAt (rcVal l) Pre Φ r

/-- **A `ReaderAndCloser` closes as its closer.** -/
def ReaderAndCloser_closer.spec : Prop :=
  ∀ (l : Loc) (v : go_etcd_io.etcd.pkg.v3.ioutil.ReaderAndCloser),
  (l ↦□ v : IProp GF) ∗ Http.readerCloser v.Closer' ⊢ Http.readerCloser (rcVal l)

end laws

end IoUtil
end EtcdGrove
end Perennial
