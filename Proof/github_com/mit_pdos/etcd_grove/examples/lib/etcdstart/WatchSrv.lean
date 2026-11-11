/-
**The server's watch facts for v3rpc's watch path** (R9, the `lean` merge, 2026-11-08). Lean-first
(no Rocq counterpart).

v3rpc's watch path (`etcd_watch_served(_chain)`, `watchStreamSpec R W`) takes `srvWOk W wsl wsN` of
the server's side `W`; client/v3's member facts tie `W`'s certified bounds and permits to the
server's (`srvKVFacts`: `W.histLb = srvApi.histLb γr on E.γs`, `W.crevOk = srvApi.crevOk γr`), so
`W` is `srvWOf E γr on` (`Served.lean`). `srvWOk_of_store` gives it from the server's store
invariant (`kvStoreInvG` at the server's witness `E.Nx = kvNx γr on` and permit `E.Cp = crevOk
γr`), the store's handle the watchable store at `wsl`, and the pure facts of a certified bound
(the server's `histLb_pure`, under `receiptBound GF ≤ 2 ^ 62`): the peek (`kvPeekG`), the namespaces (`kvsN`, `wsN`,
`mvccN` pairwise apart), `histLb`'s persistence, agreement and prefix closure (the notified log's
monotone list), `crevOk`'s persistence. `srvWOk_of_read`: the same from the auth-off read view
(`srvKVInvs`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section ns

/-- v3rpc's watch namespace is outside mvcc's. -/
theorem wsN_mvccN : (↑v3rpc.wsN : CoPset) ⊆ ⊤ \ ↑mvcc.api.mvccN := by
  intro p hp
  exact mask_ndot_ne' nroot "v3rpc" "mvcc" (by decide) p
    (nclose_subseteq (nroot .@ "v3rpc") "ws" p hp)

/-- v3rpc's watch namespace is outside the server's store invariant's. -/
theorem wsN_kvsN : (↑v3rpc.wsN : CoPset) ⊆ ⊤ \ ↑srvApi.kvsN := by
  intro p hp
  exact mask_ndot_ne' nroot "v3rpc" "server_kv_store" (by decide) p
    (nclose_subseteq (nroot .@ "v3rpc") "ws" p hp)

end ns

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- See the file header. -/
theorem srvWOk_of_store (Hp : mvcc.api.persistent.law (GF := GF))
    (Hr : mvcc.api.mvccState_reachable.law (GF := GF)) (E : apply.AEnv GF) (γr : ReadNames)
    (on : Bool) (wsl : Loc) (hkv : E.kv = v3rpc.wsIface wsl) (hNx : E.Nx = srvApi.kvNx γr on)
    (hCp : E.Cp = srvApi.crevOk γr)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    □ srvApi.kvStoreInvG (GF := GF) E.kv E.γ E.Nx E.Cp E.γs ⊢
      v3rpc.srvWOk (srvWOf E γr on) wsl v3rpc.wsN := by
  rw [hNx, hCp]
  iintro #Hs
  ihave #Hs' := Hs
  iunfold srvApi.kvStoreInvG at Hs'
  icases Hs' with ⟨#Hm, -⟩
  iunfold v3rpc.srvWOk
  simp only [srvWOf]
  isplitr; · ipureintro; exact hkv
  isplitr; · iexact Hm
  isplitr
  · iunfold v3rpc.srvPeek
    iintro !> %Em %hEm
    ihave Hpk := srvApi.kvPeekG (srvApi.kvNx γr on) (srvApi.crevOk γr) Hp Hr E.kv E.γ E.γs Em hEm $$ Hs
    imod Hpk with ⟨%σ, Hσ, Hh, Hc, -, Hcl⟩
    imodintro
    iexists σ
    simp only [srvWOf, srvApi.histLb_eq]
    iframe
  isplitr
  · ipureintro
    exact ⟨srvApi.kvsN_mvccN, wsN_mvccN, wsN_kvsN⟩
  isplitr
  · iintro !> %L #H; iexact H
  isplitr
  · iintro !> %L %L' #H #H'
    iunfold srvApi.histLb at H
    iunfold srvApi.histLb at H'
    icases H with ⟨#H, -⟩
    icases H' with ⟨#H', -⟩
    iapply mono_list_lb_valid $$ H H'
  isplitr
  · iintro !> %L %L' %hp #H
    iunfold srvApi.histLb at H
    iunfold srvApi.histLb
    icases H with ⟨#Hl, %L'', %hL'', #Hx, #Hrc, %Hlen⟩
    isplitl
    · iapply monoListLbOwn_le L' hp $$ Hl
    iexists L''
    iframe Hx Hrc
    isplitl
    · ipureintro; exact ⟨hp.trans hL''.1, hL''.2⟩
    · ipureintro; exact Hlen
  isplitr
  · iintro !> %L #H
    iapply srvApi.histLb_pure hrb γr on E.γs L $$ H
  iintro !> %c #H; iexact H

/-- **`srvWOk_of_store` from the auth-off read view** (`srvKVInvs`: the store invariant, the
witness `kvNxOff`, the permit `kvCpOk`). -/
theorem srvWOk_of_read (Hp : mvcc.api.persistent.law (GF := GF))
    (Hr : mvcc.api.mvccState_reachable.law (GF := GF)) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (wsl : Loc) (hkv : E.kv = v3rpc.wsIface wsl)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    isServerRead s E γr ⊢ v3rpc.srvWOk (srvWOf E γr false) wsl v3rpc.wsN := by
  iintro #Hrd
  ihave #Hinvs := srvKVInvs_of_read s E γr $$ Hrd
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨-, -, -, #Hs, %Hm, %HNx, -⟩
  iapply (srvWOk_of_store Hp Hr E γr false wsl hkv (by rw [HNx]; rfl) (by rw [Hm.2.2.2]; rfl) hrb)
  iexact Hs

/-- **`srvWOk_of_store` from the auth-on read view** (`srvKVInvsOn`: the store invariant, the
witness `kvNxOn` at the auth store's start, the permit `kvCpOk`). -/
theorem srvWOk_of_readOn (Hp : mvcc.api.persistent.law (GF := GF))
    (Hr : mvcc.api.mvccState_reachable.law (GF := GF)) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (wsl : Loc) (hkv : E.kv = v3rpc.wsIface wsl)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    isServerReadM true s E γr ⊢ v3rpc.srvWOk (srvWOf E γr true) wsl v3rpc.wsN := by
  iintro #Hsrd
  ihave #Hc := srvKVCoreM_of_readM true s E γr $$ Hsrd
  rw [srvKVCoreM_true]
  icases Hc with ⟨-, -, -, #Hs, -, %HNx⟩
  iunfold isServerReadM at Hsrd
  icases Hsrd with ⟨%v, Hsrd⟩
  iunfold srvReadFieldsAtM at Hsrd
  icases Hsrd with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hkvi, -⟩
  ihave #Hon := srvKVInvsM_true s E γr $$ Hkvi
  iunfold srvKVInvsOn at Hon
  icases Hon with ⟨-, -, -, -, -, %Hw, -, -⟩
  iapply (srvWOk_of_store Hp Hr E γr true wsl hkv (by rw [HNx]; rfl) (by rw [Hw.2]; rfl) hrb)
  iexact Hs

/-- **The server's KV field is the watchable store `v3rpc.Server` reads** (`srvServeFacts`' handle
and `grpcCfgOk`'s field agree). -/
theorem kv_wsIface_of_cfg (s : Loc) (E : apply.AEnv GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (C : v3rpc.GrpcCfg GF) :
    srvServeFacts s E cfg ∗ v3rpc.grpcCfgOk s C ⊢ ⌜E.kv = v3rpc.wsIface C.wsl⌝ := by
  iintro ⟨#Hf, #Hc⟩
  iunfold srvServeFacts at Hf
  icases Hf with ⟨⟨%wsl', #Ha', %He, -⟩, -⟩
  iunfold v3rpc.grpcCfgOk at Hc
  icases Hc with ⟨-, -, #Ha, -⟩
  icombine Ha' Ha gives %h
  ipureintro; rw [He]; exact h

/-- **The watch path's server facts of a started, auth-off member, at `v3rpc.Server`'s watchable
store** (`srvWOk_of_read` at `kv_wsIface_of_cfg`). -/
theorem srvWOk_of_up (Hp : mvcc.api.persistent.law (GF := GF))
    (Hr : mvcc.api.mvccState_reachable.law (GF := GF)) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (C : v3rpc.GrpcCfg GF)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    isServerRead s E γr ∗ srvServeFacts s E cfg ∗ v3rpc.grpcCfgOk s C ⊢
      v3rpc.srvWOk (srvWOf E γr false) C.wsl v3rpc.wsN := by
  iintro ⟨#Hrd, #Hf, #Hc⟩
  ihave %hkv := kv_wsIface_of_cfg s E cfg C $$ [Hf Hc]
  · iframe #
  iapply (srvWOk_of_read Hp Hr s E γr C.wsl hkv hrb) $$ Hrd

end proof

end etcdstart
end EtcdGrove
end Perennial
