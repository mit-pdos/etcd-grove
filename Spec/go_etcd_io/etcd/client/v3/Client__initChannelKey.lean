/-
`(*Client).initChannelKey(ctx, key)` (`client/v3/channel_pool.go:38`, PR #21765): validates `key`,
falls back to `c.ctx` if `ctx == nil`, acquires `c.epMu.Lock()` (`defer c.epMu.Unlock()`), checks
if `c.channels == nil` or `key` is already in `c.channels` (idempotent `return nil`), and otherwise
copies `c.endpoints`, creates a fresh `EtcdManualResolver`, dials a connection via
`c.dialWithBalancerForKey`, and inserts `channel{conn: conn, resolver: r}` into `c.channels[key]`
(or closes `r` if dialing fails). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.validateChannelKey
public import Spec.go_etcd_io.etcd.client.v3.Client__dialWithBalancer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

abbrev Client.initChannelKey.spec : Prop :=
  ∀ (c mu mref : Loc) (ctx cctx : GoInterface) (dq0 : DFrac) (key : GoString)
    (cfg : go_etcd_io.etcd.client.v3.Config) (cr : GoInterface) (esl : GoSlice)
    (eps : List GoString) (chs : GMap GoString go_etcd_io.etcd.client.v3.channel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      retryClientOk c ∗ clientF c go!"ctx" ↦{dq0} cctx ∗
      clientF c go!"epMu" ↦□ mu ∗ sync.isRWMutexGuard mu (fun _ => iprop(True)) ∗
      clientF c go!"cfg" ↦□ cfg ∗ cfg.DialOptions' ↦*□ ([] : List GoInterface) ∗
      clientF c go!"authTokenBundle" ↦□ GoInterface.nil ∗ clientF c go!"creds" ↦□ cr ∗
      clientF c go!"endpoints" ↦□ esl ∗ esl ↦*□ eps ∗ ⌜plainEndpoints eps⌝ ∗
      ⌜mref ≠ map.nil⌝ ∗ clientF c go!"channels" ↦ mref ∗ mref ↦$ chs }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"initChannelKey"))
      (Val #ctx)) (Val #key))
  {{ (err : GoInterface), RET #err;
      clientF c go!"ctx" ↦{dq0} cctx ∗ clientF c go!"channels" ↦ mref ∗
      if decide (key = go!"" ∨ key = go!"default") then
        mref ↦$ chs ∗
          ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗
            go_etcd_io.etcd.cache.v3.errorStringSpec e
      else if (chs !! key).isSome then
        ⌜err = GoInterface.nil⌝ ∗ mref ↦$ chs
      else
        (⌜err = GoInterface.nil⌝ ∗
          ∃ conn r : Loc, ⌜conn ≠ null ∧ r ≠ null⌝ ∗ isEtcdConn conn eps ∗
            mref ↦$ (<[key := go_etcd_io.etcd.client.v3.channel.mk conn r]> chs)) ∨
        (⌜err ≠ GoInterface.nil⌝ ∗ mref ↦$ chs) }}

end spec

end EtcdGrove
end Perennial
