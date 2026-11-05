/-
`(*EtcdServer).start()` (`server.go`), translated with its body: it sets the fields the server's
goroutines share and starts `run`. Lean-first (the request path's unit 4c, 2026-10-13); see
`InvStart.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StartOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthCompRows

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

/-- **`s.start()`** in both auth modes (the auth component's stage 2, 2026-11-04; until then `spec`
with auth off and `specOn` with auth on, now `specOff`/`specOn`, `ModeSpecs.lean`'s corollaries):
from the construction premise in the component `C` (`isServerBuiltC`) and the lessor finding no
lease (`acLessor C`), in the environment's mode, it sets the snapshot defaults, the wait registries
(`w`, `applyWait`), the channels `done`, `stop`, `stopping`, the server's context, the read loop's
`*Read` and the leader-change notifier, sets up `GoAttach`'s protocol, and starts `run`
(`isServerRunC C`, with the write budget `srvWTPool E` made of the `N` write tokens, D19b: under
the pure premise `receiptBound GF ≤ N + 1`); it returns the server's persistent views in the
mode (`isServerReqM`, at the wait's fresh names, and `isServerReadM`), the store's range check at a
reader's lower bound (`srvAuthLb`, trivial with auth off), and what `Start`'s goroutines and the
request path's get (`srvStarted`, at the mode's model state), and (H2, 2026-11-05) the write
budget with its register set to `GoAttach`'s receipts' name `γg.run`, with `Start`'s reader slot of
`wgMu` at `γg` (so that the storage-version monitor `Start` attaches runs with a receipt at the
registered name). A new server: the apply thread from
index `0` (each applied entry takes a write token, which bounds the applied index,
`srvWTPool_bound`). -/
abbrev EtcdServer.start.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (C : AuthC) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜E.authMode = C.mode ∧ acReceiptOk (GF := GF) C ∧ receiptBound GF ≤ N + 1 ∧ ai₀ = W64 0⌝ ∗
      isServerBuiltC C s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ∗ acLessor C s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"start")) (Val #()))
  {{ RET #(); ∃ γw : GName, isServerReqM C.isOn s E { ρ with wait := γw } ∗
      isServerReadM C.isOn s E γr ∗ srvAuthLb s E ∗
      srvStarted s γr ρ Er.RQ (kvStM C.isOn γr.kv) ∗
      ∃ (γp : WTNames) (γg : GoNames), srvWTPool E γp ∗
        dghostVar γp.reg DFrac.discard (some γg.run) ∗ srvWgReaderAt s γg }}

end spec

end EtcdGrove
end Perennial
