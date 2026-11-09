/-
## `read.NewRead(server, raft)`

**Users.** `EtcdServer.start` (`server.go:573`: `read.NewRead(s, &s.r)`, before it sets the fields
`s`'s `LeaderChanged`, `Done`, ... read). Snippet: `examples/specreq/etcdserverreq/read.go`.

**Proof sketch.** Allocates the struct with `waitC` (buffer 1) and a first notifier
(`newNotifier`); `readNew r srv rf` is the struct's ownership with `srv` and `rf` saved. The
invariants are allocated by `readNew_init`, once the caller has `readEnv` (2e's `start`, from the
server's methods and the raft wrapper's: `req/go_etcd_io_etcd_server_v3_etcdserver.md`, from 2c).

**Changes.** The old spec took the server's `Done()` contract and the notifier's ghost variable and
returned the loop's precondition as a wand over the later contracts plus the `RWMutex`'s reader
slots; restated as `readNew` and the law `readNew_init` (no reader slots: the readers' thread
tokens).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Read

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- **A new read path** over the server `srv` and raft `rf`, to be started by `readNew_init`. -/
def NewRead.spec : Prop :=
  ∀ (srv rf : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.read.NewRead)) (Val #srv)) (Val #rf))
  {{ (r : Loc), RET #r; readNew r srv rf }}

end spec
end Read
end EtcdGrove
end Perennial
