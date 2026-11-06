/-
`(*EtcdServer).GoAttach(f)` (`server.go`), translated with its body (the request path's unit 4c,
2026-10-13; names-only, an axiom, until then). Lean-first (no Rocq counterpart); see
`InvGoAttach.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 go_etcd_io.etcd.pkg.v3 go_uber_org

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.GoAttach(f)`, by a goroutine with a reader slot of `wgMu` at the protocol's names `γ`
(`srvWgReaderAt`) and one level of a thread token (below), of a
closure `f` with `P` (`{P ∗ goRunning γ} f() {goRunning γ}`): if `stopping` is closed, nothing (`P`
dropped: `f` never runs); else `f` runs in a goroutine counted by `s.wg`, with that goroutine's
receipt (`goRunning γ`), which it gives back for its `Done` (H2, 2026-11-05: so a goroutine can
deposit its receipt in a protocol of its own while it runs, and the shutdown's `goWaited` excludes
it). The caller gets its slot and its level back.

(revoke-open Q4 (i), 2026-11-06) By levels: the caller gives one level of a thread token
(`levelTok 1`), `wg.Add`'s pending deposit, back at the `go` statement (stopped: the level that
borrows `Logger()`'s `lgMu` slot from `raftPool`, `srvGoAttachOk`'s, so no `srvLgReader` is taken);
`f` runs on the fresh token's levels from 1 (`threadTokFrom 1`; level 0 is in the wait group until
its `Done`). The level is `raftPool`'s (`Net.lean`, level 1), which the stopped branch borrows with
it: a change of one moves the other. A caller with a whole token uses `wp_GoAttach_tok`
(`GoAttachTok.lean`), today's triple. -/
abbrev EtcdServer.GoAttach.spec : Prop :=
  ∀ (s : Loc) (γ : GoNames) (f : GoFunc) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvWgReaderAt s γ ∗ levelTok 1 ∗ P ∗
      {{ P ∗ goRunning γ ∗ threadTokFrom 1 }} (App (Val #f) (Val #()))
        {{ RET #(); goRunning γ ∗ threadTokFrom 1 }} }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"GoAttach")) (Val #f))
  {{ RET #(); srvWgReaderAt s γ ∗ levelTok 1 }}

end spec

end EtcdGrove
end Perennial
