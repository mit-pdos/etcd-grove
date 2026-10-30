/-
`startServer(lg)` (`examples/authkv/authkv.go`; the auth plan's E3zb, 2026-10-28): the one member
of a new cluster started with auth on -- its peer URL slice, its configuration (`common.newServer`'s,
on authkv's ports, with the simple token provider and etcd's default token TTL, `300`),
`etcdserver.NewServer`, `s.Start()`. Lean-first (no Rocq counterpart).

**The triple:** `common.StartServer.spec`'s, with auth on: given the member's ghost state with auth
on (`memberBootOn`: the start chain with the auth layer enabled, the KV invariant in the mode `on`),
the network's HTTP side, a thread token, `bootstrap`'s contract for it (`bootPremise` at the
one-member cluster `[id]`, the token `authkv` and the URLs `urls1`) and the premises the members
share: an error with the thread token, or the member started with auth on (`memberUpOn`, at the auth
names `γa` of the store `NewServer` built).

**The pure premises:** `common.StartServer.spec`'s, at authkv's addresses.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- See the file header. -/
abbrev startServer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (lg : Loc)
    (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString) (id : w64)
    (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
  threadBound GF ≤ 2 ^ 31 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.vs = [id] → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://127.0.0.1:23926" ∈ dir id →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.dbOpensOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv ∗
      threadTok ∗
      common.bootPremise N [id] bootLog ctxs dir go!"authkv" go!"authkv"
        (common.urls1 go!"authkv" go!"127.0.0.1:23926" go!"127.0.0.1:23916") id ∗
      common.commonPremises ∗ context.isClosedchanInit ∗
      common.memberBootOn γ ctxs ρ E₀ Φs id ∗
      netHttpOk γn id }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.startServer)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ γa : auth.AuthNames, common.memberUpOn s ρ E₀ lg γn id γa) }}

end spec

end authkv
end EtcdGrove
end Perennial
