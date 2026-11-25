/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Spec/client.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; statements the lab's (the configured
addresses `VsrWire.addrs`; the JSON vocabulary `Spec/jsonlib.lean`'s, the logger `Dsverify/Spec/log/slog/Logger.lean`'s).
-/
/-
Cross-package specs of `pkg/client` (called by the adapter `examples/vsrnet`): the `*Client`
(`isClient cl γ c st`, exclusive) of client id `c` with abstract state `st`: its request number
`n` and its pending request (`some op`: request `n` with operation `op`, from `Request` until
`CheckResult` returns its reply). The client's request counter `nextReq γ c _` is not inside
(the adapter keeps it and registers each request before `Request`).

Specs: `New`, `Request`, `Submit`, `Run`, `CheckResult`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.network
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Dsverify.Spec.log.slog.Logger
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.client.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A client's abstract state: its request number and its pending request's operation. -/
structure client.St where
  n : Nat
  pend : Option GoString

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : client.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

/-- The `*Client` `cl` is client `c` of the system `γ` in state `st` (exclusive).
-- sealed: the package's choice -/
def client.isClient (cl : Loc) (γ : VsrGhost.Names) (c : Nat) (st : client.St) :
    IProp GF :=
  iprop(∃ (v : client.Client) (mems : List ipv4port.IPv4Port) (F : List w8 → Bool → w64 × w64)
      (jc : models_lab.jsoncodec.JsonCodec GF),
    cl ↦ v ∗
    ⌜uint.nat v.state'.ID' = c ∧ uint.nat v.state'.RequestNumber' = st.n ∧ 0 < mems.length⌝ ∗
    v.state'.LastKnownClusterMembers' ↦*□ mems ∗
    ([∗list] a ∈ mems, network.netAddrOk v.net' a) ∗
    network.isNet v.net' γ ∗ network.netSender v.net' ∗ network.netProtos γ ∗
    ⌜time.isTime v.time'⌝ ∗ log.slog.isLogger v.logger' ∗
    encoding.json.codecSet (GF := GF) ∗ encoding.json.kitCodecOk (jc := jc) F ∗
    queue.isQueue events.Reply.ty v.internal'.response'
      (fun rep : events.Reply => VsrGhost.fact γ (.msg (.reply (uint.nat rep.ID')
        (uint.nat rep.ClientID') (uint.nat rep.ViewNum') rep.Result'))) ∗
    match st.pend with
    | none => iprop(⌜v.internal'.request' = null ∧ v.internal'.result' = null⌝)
    | some op => iprop(⌜PlainStr op ∧ (VsrWire.line (.request st.n c op)).length < 2 ^ 60⌝ ∗
      VsrGhost.fact γ (.msg (.request st.n c op)) ∗
      ((∃ (r : Loc) (x : events.Request),
          ⌜v.internal'.request' = r ∧ v.internal'.result' = null ∧ events.reqIs x st.n c op⌝ ∗
          r ↦□ x ∗ ∃ tst : GoInterface, time.isTimer v.internal'.requestTimer' tst) ∨
       (∃ (rp : Loc) (rep : events.Reply), ⌜v.internal'.request' = null ∧
          v.internal'.result' = rp ∧ uint.nat rep.ID' = st.n ∧ uint.nat rep.ClientID' = c⌝ ∗
          rp ↦ rep ∗
          VsrGhost.fact γ (.msg (.reply st.n c (uint.nat rep.ViewNum') rep.Result'))))))

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : client.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]
variable [models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true

/-- `New(cfg)`: client `cfg.ID` over the network `cfg.Network` (whose sender right it gets),
the members `cfg.Members` configured addresses (at least one), a `*Real` time and a logger; the
JSON codec registered (with its scanner `F`) and the addresses' protocols. No error, the client
with request number 0 and no request pending. -/
abbrev client.New.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (cfg : client.Config) (γ : VsrGhost.Names) (dq : DFrac)
    (ms : List GoString),
  0 < ms.length → ms.length < 2 ^ 62 → (∀ a ∈ ms, a ∈ VsrWire.addrs) → time.isTime cfg.Time' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.client ∗
      cfg.Members' ↦*{dq} ms ∗ network.isNet cfg.Network' γ ∗ network.netSender cfg.Network' ∗
      network.netProtos γ ∗ log.slog.isLogger cfg.Logger' ∗
      encoding.json.codecSet (GF := GF) ∗ encoding.json.kitCodecOk F }}
    (App (Val (@! client.New)) (Val #cfg))
  {{ (cl : Loc), RET (PairV #cl #(interface.nil : GoInterface));
      cfg.Members' ↦*{dq} ms ∗ client.isClient cl γ (uint.nat cfg.ID') ⟨0, none⟩ }}

/-- `cl.Request(op)`, no request pending, the request `n + 1` valid, `op` plain (the codec
encodes it; the caller has it from `VsrGhost.fact_plain`): it is pending (the result says
whether its first send succeeded; it is pending either way). -/
abbrev client.Client.Request.spec : Prop :=
  ∀ (cl : Loc) (γ : VsrGhost.Names) (c n : Nat) (op : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.client ∗
      ⌜n + 1 < 2 ^ 64⌝ ∗ ⌜PlainStr op⌝ ∗ ⌜MsgBound (.request (n + 1) c op)⌝ ∗
      ⌜(VsrWire.line (.request (n + 1) c op)).length < 2 ^ 60⌝ ∗
      client.isClient cl γ c ⟨n, none⟩ ∗ VsrGhost.fact γ (.msg (.request (n + 1) c op)) }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"Request")) (Val #op))
  {{ (b : Bool), RET #b; client.isClient cl γ c ⟨n + 1, some op⟩ }}

/-- `cl.Submit(ev)`, an event some `*TCP` of `γ` received. -/
abbrev client.Client.Submit.spec : Prop :=
  ∀ (cl : Loc) (γ : VsrGhost.Names) (c : Nat) (st : client.St) (tcp : Loc)
    (ev : events.NetworkEvent),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.client ∗
      client.isClient cl γ c st ∗ network.netEvOk γ tcp ev }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"Submit")) (Val #ev))
  {{ RET #(); client.isClient cl γ c st }}

/-- `cl.Run()`: one round (a resend at the timeout, one submitted reply processed). -/
abbrev client.Client.Run.spec : Prop :=
  ∀ (cl : Loc) (γ : VsrGhost.Names) (c : Nat) (st : client.St),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.client ∗
      client.isClient cl γ c st }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"Run")) (Val #()))
  {{ RET #(); client.isClient cl γ c st }}

/-- `cl.CheckResult()`: `(rep, true)`, the reply of the pending request (valid: a reply to
request `n` of `c`), which is no longer pending; or `(_, false)`, nothing changed. -/
abbrev client.Client.CheckResult.spec : Prop :=
  ∀ (cl : Loc) (γ : VsrGhost.Names) (c : Nat) (st : client.St),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.client ∗
      client.isClient cl γ c st }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"CheckResult")) (Val #()))
  {{ (rep : events.Reply) (ok : Bool), RET (PairV #rep #ok);
      if ok then
        ⌜st.pend.isSome ∧ uint.nat rep.ID' = st.n ∧ uint.nat rep.ClientID' = c⌝ ∗
        client.isClient cl γ c ⟨st.n, none⟩ ∗
        VsrGhost.fact γ (.msg (.reply st.n c (uint.nat rep.ViewNum') rep.Result'))
      else client.isClient cl γ c st }}

end spec

end Perennial.github_com.tangledbytes.go_vsr.pkg
