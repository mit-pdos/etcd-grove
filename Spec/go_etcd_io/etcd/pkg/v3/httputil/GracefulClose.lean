/-
## `httputil.GracefulClose(resp)`: assumed

**Users.** `streamReader.dial` (`rafthttp/stream.go:615,622,631,642,675`: a response it will not
use, its body unread or read), the snapshot sender's timeout (`snapshot_sender.go:169`, from a
`time.AfterFunc` goroutine **while the sender's goroutine reads the body**: see Margin). Snippet:
`ioutil.go` (`ReqGracefulClose`).

**Assumed** (names only). True of the code (`httputil.go:20-28`): `io.Copy(io.Discard, resp.Body)`
reads the body to its end or an error (`Read`s of the body: 2f's `readerAt_read`), then
`resp.Body.Close()` (`readerAt_close`); nothing panics, the errors are dropped.

**Changes.** From `specs-ref`'s `GracefulClose.lean` (`respReadAny`, a reader without a guarantee,
shared with a concurrent reader): the body's reader is taken, owned.

**Margin.** The snapshot sender's use is **not covered**: its drain and the sender's `io.ReadAll`
read one body from two goroutines, so the bytes either sees are not a prefix of what the handler
wrote (the drain steals some), and `readerAt`'s knowledge would be false for the sender. A shared
reader of trivial knowledge would serve it; that is 2f's vocabulary (`req/net_http.md`, "from 4b").
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.httputil.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace HttpUtil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.httputil.Assumptions]

/-- **Drains and closes a response's body**, the reader's owner's. -/
def GracefulClose.spec : Prop :=
  ∀ (resp : Loc) (st : w64) (hc : List (GoString × GoString)) (rd : GoInterface)
    (Pre Φ : List w8 → IProp GF) (r : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.httputil ∗ Http.respAt resp st hc rd ∗
      Http.readerCloser rd ∗ Http.readerAt rd Pre Φ r }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.httputil.GracefulClose)) (Val #resp))
  {{ RET #(); True }}

end spec
end HttpUtil
end EtcdGrove
end Perennial
