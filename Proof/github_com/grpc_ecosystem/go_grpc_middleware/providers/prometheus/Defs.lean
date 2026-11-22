/-
grpc-prometheus's server-metrics options (`ServerMetricsOption`, `func(*serverMetricsConfig)`), as
`NewServerMetrics` takes them: `promSrvMetricsOpt o` (persistent), `o` sets the config's histogram
fields as `WithServerHandlingTimeHistogram()` does (providers/prometheus v1.1.0,
`server_options.go:42-47`: `histogramOpts` to its (empty) options, `enableHistogram` to `true`) and
touches nothing else. Lean-first (prove-metrics3, 2026-11-21: until then an opaque `Prop`, a
trust-boundary axiom of `InvGrpcServer.lean`).

(prom-registry, route (b), 2026-11-22) The server metrics' descriptors as prometheus's default registry reads
them (`srvDescsOk`: `NewServerMetrics`' post says its collector describes such descriptors) and the rights
to register them (`grpcKeys`, the IDs either choice of the histogram option registers: `v3rpc`'s, held by
`getServerMetrics`' lock until it registers).
-/
module

public import GeneratedProof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus
public import Perennial.Proof.ProofPrelude
public import Proof.github_com.prometheus.client_golang.prometheus.RegInv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus

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

/-! ## The server metrics' descriptors (prom-registry, route (b), 2026-11-22) -/

/-- **The server metrics' fully-qualified names, in `Describe`'s order** (providers/prometheus v1.1.0,
`server_metrics.go:89-97`: `serverStartedCounter`, `serverHandledCounter`, `serverStreamMsgReceived`,
`serverStreamMsgSent`, and, when the histogram is enabled, `serverHandledHistogram`). With no counter or
histogram options and no context labels (`promSrvMetricsOpt` sets none) each is label-free (no const labels:
the variable labels enter only the descriptor's dim hash). -/
def grpc_prometheus.srvNames (hist : Bool) : List GoString :=
  [go!"grpc_server_started_total", go!"grpc_server_handled_total",
   go!"grpc_server_msg_received_total", go!"grpc_server_msg_sent_total"] ++
  (if hist then [go!"grpc_server_handling_seconds"] else [])

/-- **The server metrics' descriptors**, as `Register` reads them: of the names `srvNames hist` in order,
each label-free (its ID its name's `descId`) and valid (`err` nil). -/
def grpc_prometheus.srvDescsOk [GooseExts] (hist : Bool)
    (ds : List github_com.prometheus.client_golang.prometheus.Desc) : Prop :=
  ds.map (·.fqName') = grpc_prometheus.srvNames hist ∧
    ∀ d ∈ ds, d.id' = prometheus.descId d.fqName' ∧ d.err' = (interface.nil : GoInterface)

/-- The IDs `Register` adds for the server metrics (`descKeys` of their descriptors, which depends on the
IDs only): their descriptor IDs and, unless one of them, their XOR. -/
def grpc_prometheus.srvKeys (hist : Bool) : List w64 :=
  let ids := (grpc_prometheus.srvNames hist).map prometheus.descId
  if prometheus.xorAll ids ∈ ids then ids else ids ++ [prometheus.xorAll ids]

/-- The four counter vectors' descriptor IDs. -/
def grpc_prometheus.ids4 : List w64 :=
  [go!"grpc_server_started_total", go!"grpc_server_handled_total",
   go!"grpc_server_msg_received_total", go!"grpc_server_msg_sent_total"].map prometheus.descId

/-- The histogram vector's descriptor ID. -/
def grpc_prometheus.id5 : w64 := prometheus.descId go!"grpc_server_handling_seconds"

/-- The collector ID without the histogram (the XOR of `ids4`). -/
def grpc_prometheus.x4 : w64 := prometheus.xorAll grpc_prometheus.ids4

/-- The collector ID with the histogram. -/
def grpc_prometheus.x5 : w64 := prometheus.xorAll (grpc_prometheus.ids4 ++ [grpc_prometheus.id5])

/-- **The rights `getServerMetrics` holds until it registers** (`v3rpc.metricsP`): the IDs of either
choice of the histogram option, which is made at run time (`Server`'s `ServerConfig`). -/
def grpc_prometheus.grpcKeys : List w64 :=
  grpc_prometheus.ids4 ++ [grpc_prometheus.x4, grpc_prometheus.id5, grpc_prometheus.x5]

/-! The kernel hashes the five names here, once, in small lemmas (never inside a large proof). -/

theorem grpc_prometheus.srvKeys_false :
    grpc_prometheus.srvKeys false = grpc_prometheus.ids4 ++ [grpc_prometheus.x4] := by
  decide +kernel

theorem grpc_prometheus.srvKeys_true :
    grpc_prometheus.srvKeys true =
      grpc_prometheus.ids4 ++ [grpc_prometheus.id5, grpc_prometheus.x5] := by
  decide +kernel

theorem grpc_prometheus.srvIds_nodup (hist : Bool) :
    ((grpc_prometheus.srvNames hist).map prometheus.descId).Nodup := by
  cases hist <;> decide +kernel

theorem grpc_prometheus.srvNames_nodup (hist : Bool) : (grpc_prometheus.srvNames hist).Nodup := by
  cases hist <;> decide +kernel

theorem grpc_prometheus.srvNames_not_builtin (hist : Bool) :
    ∀ n ∈ grpc_prometheus.srvNames hist, n ∉ prometheus.builtinNames := by
  cases hist <;> decide +kernel

theorem grpc_prometheus.srvNames_length (hist : Bool) : (grpc_prometheus.srvNames hist).length ≤ 5 := by
  cases hist <;> decide

/-- The descriptors' IDs are their names' (`srvDescsOk`). -/
theorem grpc_prometheus.srvDescs_ids [GooseExts] (hist : Bool)
    (ds : List github_com.prometheus.client_golang.prometheus.Desc)
    (h : grpc_prometheus.srvDescsOk hist ds) :
    ds.map (·.id') = (grpc_prometheus.srvNames hist).map prometheus.descId := by
  rw [← h.1, List.map_map]
  exact List.map_congr_left (fun d hd => (h.2 d hd).1)

/-- The server metrics' descriptors are accepted (`descsOk`). -/
theorem grpc_prometheus.srvDescs_descsOk [GooseExts] (hist : Bool)
    (ds : List github_com.prometheus.client_golang.prometheus.Desc)
    (h : grpc_prometheus.srvDescsOk hist ds) : prometheus.descsOk ds := by
  have hl : ds.length = (grpc_prometheus.srvNames hist).length := by
    rw [← h.1, List.length_map]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro he
    rw [he] at hl
    cases hist <;> simp [grpc_prometheus.srvNames] at hl
  · have := grpc_prometheus.srvNames_length hist
    omega
  · rw [h.1]; exact grpc_prometheus.srvNames_nodup hist
  · rw [grpc_prometheus.srvDescs_ids hist ds h]; exact grpc_prometheus.srvIds_nodup hist
  · intro d hd
    refine ⟨(h.2 d hd).2, (h.2 d hd).1, ?_⟩
    apply grpc_prometheus.srvNames_not_builtin hist
    rw [← h.1]
    exact List.mem_map_of_mem hd

/-- The keys `Register` adds for them. -/
theorem grpc_prometheus.srvDescs_keys [GooseExts] (hist : Bool)
    (ds : List github_com.prometheus.client_golang.prometheus.Desc)
    (h : grpc_prometheus.srvDescsOk hist ds) :
    prometheus.descKeys ds = grpc_prometheus.srvKeys hist := by
  unfold prometheus.descKeys grpc_prometheus.srvKeys
  rw [grpc_prometheus.srvDescs_ids hist ds h]

section toks
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The rights `getServerMetrics` holds give those its registration takes, whichever the option. -/
theorem grpc_prometheus.grpcKeys_srv (γ : GName) (hist : Bool) :
    prometheus.idToks (GF := GF) γ grpc_prometheus.grpcKeys ⊢
      prometheus.idToks (GF := GF) γ (grpc_prometheus.srvKeys hist) := by
  unfold grpc_prometheus.grpcKeys
  cases hist
  · rw [grpc_prometheus.srvKeys_false]
    iintro H
    icases (prometheus.idToks_app (GF := GF) γ _ _).1 $$ H with ⟨H4, Hr⟩
    icases (prometheus.idToks_cons (GF := GF) γ _ _).1 $$ Hr with ⟨Hx, -⟩
    iapply (prometheus.idToks_app (GF := GF) γ _ _).2
    iframe H4
    iapply (prometheus.idToks_singleton (GF := GF) γ _).2
    iexact Hx
  · rw [grpc_prometheus.srvKeys_true]
    iintro H
    icases (prometheus.idToks_app (GF := GF) γ _ _).1 $$ H with ⟨H4, Hr⟩
    icases (prometheus.idToks_cons (GF := GF) γ _ _).1 $$ Hr with ⟨-, Hr⟩
    iapply (prometheus.idToks_app (GF := GF) γ _ _).2
    iframe H4; iexact Hr

end toks

end EtcdGrove
end Perennial
