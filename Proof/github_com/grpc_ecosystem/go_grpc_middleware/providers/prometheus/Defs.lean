/-
grpc-prometheus's server-metrics options (`ServerMetricsOption`, `func(*serverMetricsConfig)`), as
`NewServerMetrics` takes them: `promSrvMetricsOpt o` (persistent), `o` sets the config's histogram
fields as `WithServerHandlingTimeHistogram()` does (providers/prometheus v1.1.0,
`server_options.go:42-47`: `histogramOpts` to its (empty) options, `enableHistogram` to `true`) and
touches nothing else. Lean-first (prove-metrics3, 2026-11-21: until then an opaque `Prop`, a
trust-boundary axiom of `InvGrpcServer.lean`).

(prom-registry, 2026-11-22) The server metrics' descriptors as prometheus's default registry sees them
(`srvDescs`: `NewServerMetrics`' post says its collector describes them) and the rights to register
them (`grpcKeys`, the IDs either choice of the histogram option registers: `v3rpc`'s, held by
`getServerMetrics`' lock until it registers).
-/
module

public import GeneratedProof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus
public import Perennial.Proof.ProofPrelude
public import Proof.github_com.prometheus.client_golang.prometheus.Registry

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus
open _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`o` is one of grpc-prometheus's own server-metrics options** (persistent; see the file
header): applied to a config `c`, it sets `c.histogramOpts` to the empty options and
`c.enableHistogram` to `true`, and returns. -/
def promSrvMetricsOpt (o : GoFunc) : IProp GF :=
  iprop(□ ∀ (c : Loc) (ho : GoSlice) (eh : Bool),
    {{ c.[serverMetricsConfig, go!"histogramOpts"] ↦ ho ∗
        c.[serverMetricsConfig, go!"enableHistogram"] ↦ eh }}
      (App (Val #o) (Val #c))
    {{ RET #(); c.[serverMetricsConfig, go!"histogramOpts"] ↦ slice.nil ∗
        c.[serverMetricsConfig, go!"enableHistogram"] ↦ true }})

instance promSrvMetricsOpt_persistent (o : GoFunc) :
    Persistent (promSrvMetricsOpt (GF := GF) o) := by
  unfold promSrvMetricsOpt; infer_instance

end defs

/-! ## The server metrics' descriptors (prom-registry, 2026-11-22) -/

/-- **The server metrics' fully-qualified names, in `Describe`'s order** (providers/prometheus
v1.1.0, `server_metrics.go`: `serverStartedCounter`, `serverHandledCounter`,
`serverStreamMsgReceived`, `serverStreamMsgSent`, and, when the histogram is enabled,
`serverHandledHistogram`). With no counter or histogram options (`promSrvMetricsOpt` sets none)
each is label-free (no const labels: its variable labels enter only the descriptor's dim hash). -/
def grpc_prometheus.srvNames (hist : Bool) : List GoString :=
  [go!"grpc_server_started_total", go!"grpc_server_handled_total",
   go!"grpc_server_msg_received_total", go!"grpc_server_msg_sent_total"] ++
  (if hist then [go!"grpc_server_handling_seconds"] else [])

/-- The descriptors the server metrics describe (`hist`: the histogram enabled), with dim hashes
`dh` (one per name). -/
def grpc_prometheus.srvDescs [GooseExts] (hist : Bool) (dh : GoString → w64) : List promreg.Desc :=
  (grpc_prometheus.srvNames hist).map (fun n => prometheus.nameDesc n (dh n))

/-- The IDs `Register` adds for the server metrics (`promreg.descKeys` of `srvDescs`, which depends on
the IDs only): their distinct descriptor IDs and, unless one of them, their XOR. -/
def grpc_prometheus.srvKeys (hist : Bool) : List w64 :=
  let ids := ((grpc_prometheus.srvNames hist).map prometheus.descId).eraseDups
  if ids.foldl (· ^^^ ·) 0 ∈ ids then ids else ids ++ [ids.foldl (· ^^^ ·) 0]

/-- The four counter vectors' descriptor IDs. -/
def grpc_prometheus.ids4 : List w64 :=
  [go!"grpc_server_started_total", go!"grpc_server_handled_total",
   go!"grpc_server_msg_received_total", go!"grpc_server_msg_sent_total"].map prometheus.descId

/-- The histogram vector's descriptor ID. -/
def grpc_prometheus.id5 : w64 := prometheus.descId go!"grpc_server_handling_seconds"

/-- The collector ID without the histogram (the XOR of `ids4`). -/
def grpc_prometheus.x4 : w64 := grpc_prometheus.ids4.foldl (· ^^^ ·) 0

/-- The collector ID with the histogram. -/
def grpc_prometheus.x5 : w64 := (grpc_prometheus.ids4 ++ [grpc_prometheus.id5]).foldl (· ^^^ ·) 0

/-- **The rights `getServerMetrics` holds until it registers** (`v3rpc.metricsP`): the IDs of either
choice of the histogram option, which is made at run time (`Server`'s `ServerConfig`). -/
def grpc_prometheus.grpcKeys : List w64 :=
  grpc_prometheus.ids4 ++ [grpc_prometheus.x4, grpc_prometheus.id5, grpc_prometheus.x5]

theorem grpc_prometheus.srvKeys_false :
    grpc_prometheus.srvKeys false = grpc_prometheus.ids4 ++ [grpc_prometheus.x4] := by
  decide +kernel

theorem grpc_prometheus.srvKeys_true :
    grpc_prometheus.srvKeys true =
      grpc_prometheus.ids4 ++ [grpc_prometheus.id5, grpc_prometheus.x5] := by
  decide +kernel

/-- (Proved by unfolding `nameDesc` only: the kernel must never unfold `descId` on a variable.) -/
theorem grpc_prometheus.nameDesc_ID [GooseExts] (n : GoString) (dh : w64) :
    (prometheus.nameDesc n dh).ID' = prometheus.descId n := by
  rw [prometheus.nameDesc.eq_def]

theorem grpc_prometheus.srvDescs_IDs [GooseExts] (hist : Bool) (dh : GoString → w64) :
    (grpc_prometheus.srvDescs hist dh).map (·.ID') =
      (grpc_prometheus.srvNames hist).map prometheus.descId := by
  unfold grpc_prometheus.srvDescs
  rw [List.map_map]
  apply List.map_congr_left
  intro n _
  exact grpc_prometheus.nameDesc_ID n (dh n)

theorem grpc_prometheus.srvDescs_keys [GooseExts] (hist : Bool) (dh : GoString → w64) :
    promreg.descKeys (grpc_prometheus.srvDescs hist dh) = grpc_prometheus.srvKeys hist := by
  unfold promreg.descKeys grpc_prometheus.srvKeys
  rw [grpc_prometheus.srvDescs_IDs]

theorem grpc_prometheus.srvNames_not_builtin (hist : Bool) :
    ∀ n ∈ grpc_prometheus.srvNames hist, n ∉ promreg.builtinNames := by
  cases hist <;> decide +kernel

/-- The server metrics' descriptors are accepted (`descsOk`). -/
theorem grpc_prometheus.srvDescs_ok [GooseExts] (hist : Bool) (dh : GoString → w64) :
    promreg.descsOk prometheus.descId (grpc_prometheus.srvDescs hist dh) := by
  unfold grpc_prometheus.srvDescs
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    simp only [List.mem_map] at hd
    obtain ⟨n, hn, rfl⟩ := hd
    refine ⟨?_, grpc_prometheus.nameDesc_ID n (dh n), ?_⟩
    · rw [prometheus.nameDesc.eq_def]
    · rw [prometheus.nameDesc.eq_def]
      exact grpc_prometheus.srvNames_not_builtin hist n hn
  · intro d hd d' hd' he
    simp only [List.mem_map] at hd hd'
    obtain ⟨n, -, rfl⟩ := hd
    obtain ⟨n', -, rfl⟩ := hd'
    rw [prometheus.nameDesc.eq_def, prometheus.nameDesc.eq_def] at he ⊢
    simp only at he ⊢
    rw [he]
  · cases hist <;> simp [grpc_prometheus.srvNames]

section toks
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The rights `getServerMetrics` holds give those its registration takes, whichever the option. -/
theorem grpc_prometheus.grpcKeys_srv (hist : Bool) (dh : GoString → w64) :
    promreg.idToks (GF := GF) grpc_prometheus.grpcKeys ⊢
      promreg.idToks (GF := GF) (promreg.descKeys (grpc_prometheus.srvDescs hist dh)) := by
  rw [grpc_prometheus.srvDescs_keys]
  unfold grpc_prometheus.grpcKeys
  cases hist
  · rw [grpc_prometheus.srvKeys_false]
    iintro H
    ihave ⟨H4, Hr⟩ := (promreg.idToks_app (GF := GF) _ _).1 $$ H
    ihave ⟨Hx, -⟩ := (promreg.idToks_cons (GF := GF) _ _).1 $$ Hr
    iapply (promreg.idToks_app (GF := GF) _ _).2
    iframe H4
    iapply (promreg.idToks_cons (GF := GF) _ []).2
    iframe Hx
    unfold promreg.idToks; iapply BigSepL.bigSepL_nil.2; iempintro
  · rw [grpc_prometheus.srvKeys_true]
    iintro H
    ihave ⟨H4, Hr⟩ := (promreg.idToks_app (GF := GF) _ _).1 $$ H
    ihave ⟨-, Hr⟩ := (promreg.idToks_cons (GF := GF) _ _).1 $$ Hr
    iapply (promreg.idToks_app (GF := GF) _ _).2
    iframe H4; iexact Hr

end toks

end EtcdGrove
end Perennial
