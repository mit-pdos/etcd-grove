/-
`s.Backend()` (`server.go`): `s.be` under `s.bemu`'s read lock. Lean-first (no Rocq counterpart);
the request path's unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.Backend()`, with a reader slot of `s.bemu` (given back): some backend the server held, with
its persistent facts (`srvBeRO`; D22 receiver epochs, S7b: nothing about which backend is current
once `RUnlock` returns, `applySnapshot` may swap it then). -/
abbrev EtcdServer.Backend.spec : Prop :=
  ∀ (s : Loc) (γbe : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvBemuReaderAt s γbe }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Backend")) (Val #()))
  {{ (b : GoInterface), RET #b; srvBemuReaderAt s γbe ∗
      ∃ d : mvcc.KBReal, ⌜b = srvBeIface d.be⌝ ∗ srvBeRO d }}

end spec

end EtcdGrove
end Perennial
