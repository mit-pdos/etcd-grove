/-
`(*EtcdServer).Start()` (`server.go`), translated with its body: `start`, then ten goroutines
through `GoAttach`. Lean-first (the request path's unit 4c, 2026-10-13); see `InvStart.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStorageVersion
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvMonitors
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.MonitorsOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StartOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunOn
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

/-- **`s.Start()`** in both auth modes (the auth component's stage 2, 2026-11-04; until then `spec`
with auth off and `specOn` with auth on, now `specOff`/`specOn`, `ModeSpecs.lean`'s corollaries):
from `start.spec`'s premises (the construction premise in the component `C`, the lessor finding no
lease), the caller's thread token and two reader slots of `s.lgMu` (one for its `GoAttach`es, given
back; one for `monitorFileDescriptor`'s goroutine, which calls `Logger()`): `start`, then the read
loop (`LinearizableReadLoop`, verified) and nine names-only monitors (trust-boundary contracts)
attached; it returns the server's views in the mode (`isServerReqM`, `isServerReadM`), the store's
range check at a reader's lower bound (`srvAuthLb`, trivial with auth off), and the slots left for
request goroutines (`srvStartReaders`, the leader-change notifier's readers), and (R2c-4)
`start`'s right to stop the server (`srvStopRight`; a caller that never stops drops it). -/
abbrev EtcdServer.Start.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (C : AuthC) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜E.authMode = C.mode ∧ acReceiptOk (GF := GF) C ∧ receiptBound GF ≤ N + 1 ∧ ai₀ = W64 0⌝ ∗
      isServerBuiltC C s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ∗ acLessor C s ∗ threadTok ∗
      srvLgReader s ∗ srvLgReader s ∗
      -- (D19i part 2) the storage version monitor's backend access (`NewServer`'s)
      srvSVRes s E ∗
      -- (audit B4a, D19m) the hash and downgrade monitors off, and `monitorDowngrade`'s `lgMu`
      -- reader slot (`NewServer`'s `srvMonitorCfg`, `srvMonitorsOff_of`)
      srvMonitorsOff s ∗ srvLgReader s ∗
      -- (2026-10-23) `publishV3`'s right to close `readych` (`NewServer`'s)
      srvReadyCloser s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
  {{ RET #(); ∃ γw : GName, isServerReqM C.isOn s E { ρ with wait := γw } ∗
      isServerReadM C.isOn s E γr ∗ srvAuthLb s E ∗
      srvGoRes s ∗ srvLgReader s ∗ srvStartReaders s γr ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (),
        ∃ n : Loc, srvLeaderChangedAddr s ↦□ n ∗ notifyReader n) ∗
      ∃ dd : GoString, srvStopRight s E ρ.rd.raft.raft ρ γn.id dd }}

end spec

end EtcdGrove
end Perennial
