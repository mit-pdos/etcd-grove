/-
Lean-first (no Rocq counterpart).

# k8setcd3: `Main`'s named premises (stage 6g)

`k8setcd3`'s `Main` starts the one-member server as `examples/etcd/txnlin`'s does (`etcdstart.StartServer`,
`etcdstart.Serve`), on other ports and names, so its premises are putget's (`Proof/.../putget/Defs.lean`, whose header explains each) at
`k8setcd3`'s configuration: `cfgOk` (member and cluster token `k8setcd3`, data directory `k8s_etcd3.etcd`,
raft's clock), `urlsOk` (peer URL `http://127.0.0.1:23906`, client URL `http://127.0.0.1:23896`)
and the peer directory `k8setcd3Dir`. The pure facts (`etcd_putget.BootFacts`), the conf-change policy
(`etcd_putget.ccOk`) are putget's and the allocation (`etcdstart.alloc1`) the shared start's, which name no
configuration.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget.Defs
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- `Main`'s peer URL, `http://127.0.0.1:23906`. -/
abbrev peerURL : _root_.Perennial.net.url.URL := etcdstart.httpURL go!"127.0.0.1:23906"

/-- `Main`'s client URL, `http://127.0.0.1:23896`. -/
abbrev clientURL : _root_.Perennial.net.url.URL := etcdstart.httpURL go!"127.0.0.1:23896"

/-- **The URLs of `Main`'s configuration**: the peer URLs `[peerURL]`, the client URLs
`[clientURL]`, the initial cluster's map `{k8setcd3 ↦ [peerURL]}`. -/
abbrev urlsOk (U : BootURLs) : Prop := etcdstart.urls1 go!"k8setcd3" go!"127.0.0.1:23906" go!"127.0.0.1:23896" U

/-- **The peer-URL directory of `Main`'s cluster**: its one member's peer URL, of the
member `id` only (`dirOne`; 2026-10-24, rafthttp stage 6d; until then every id's). -/
abbrev k8setcd3Dir (id : w64) : w64 → List GoString := etcdstart.dir1 go!"127.0.0.1:23906" id

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The configuration `Main` passes to `NewServer`**, by its scalar fields: member `k8setcd3` of a
new cluster with token `k8setcd3`, data directory `k8s_etcd3.etcd`, raft's clock `100` ms and `10`
ticks. -/
abbrev cfgOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  etcdstart.cfgOk go!"k8setcd3" go!"k8setcd3" cfg

/-- **`Main`'s named premises** (persistent): putget's (`etcd_putget.premises`) at `k8setcd3`'s
configuration, URLs and peer directory. -/
abbrev premises (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) :
    IProp GF :=
  etcdstart.premises go!"k8setcd3" go!"127.0.0.1:23906" go!"127.0.0.1:23896" N id ctxs boot

omit package_sem in
/-- **The client's `ctx` field** (read-only; `etcd3.New` reads it through `c.Ctx()`): a marked
`sorry` until the client's `New` spec gives it ("From the etcd client proof", item 6 of
`notes/k8s-etcd3-plan.md`). -/
theorem client_ctx_field (cl : Loc) (eps : List GoString) (V : client.WEnv GF) :
    isNewClient cl eps V ⊢
      ∃ cx : GoInterface, structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" cl ↦□ cx := by
  sorry

instance premises_persistent (N : Nat) (id : w64) (ctxs : List (List w8))
    (boot : List LogEntry) : Persistent (premises (GF := GF) N id ctxs boot) := by
  unfold premises; infer_instance

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
