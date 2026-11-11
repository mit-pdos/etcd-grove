/-
**The auto-compactor's environment on the server** (M2, `notes/m2-plan.md`, S4; review round 1,
S3-3): the laws that make the server what the frozen compactor contracts take, so that
`EtcdServer.Compact.spec` is checked against `v3compactor.compactableOk`:

* `errTreeOk_of_applyErrIs`, `errTreeOk_nil`: an error the request path reports, or `nil`, is one
  the compactor's `errors.Is(err, ErrCompacted)` can test (`v3compactor.errTreeOk`);
* `compactableOk_server`: the server is a `Compactable` for the compactor's revision permit over
  `srvRevLb` (a permit's `□ RevLb (r + ret)` gives `r` reached, what `Compact.spec` takes), with the
  resource every call gives back (the caller's reader slots, a thread token and a reader token of
  the store);
* `revGetterOk_server`: the server's KV (`s.kv`) is the compactor's `RevGetter` over `srvRevLb`
  (`KV.Rev.contract`, over mvcc's API since the `lean` merge), borrowing the same resource.

Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Compact
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreCore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CompactMode

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3 go_etcd_io.etcd.server.v3.etcdserver

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **An error the request path reports is one `errors.Is` can test** (the compactor's
`errTreeOk`: `applyErrIs`'s tree, whose target condition `ptrTarget` is the compactor's). -/
theorem errTreeOk_of_applyErrIs (err : GoInterface) :
    applyErrIs (GF := GF) err ⊢ v3compactor.errTreeOk err := by
  iintro #H
  ihave #Ht := applyErrIs_tree err $$ H
  iunfold v3compactor.errTreeOk
  imodintro
  iExactEq Ht; rfl

/-- `nil` is one too. -/
theorem errTreeOk_nil : ⊢ v3compactor.errTreeOk (GF := GF) GoInterface.nil := by
  iintro
  iapply errTreeOk_of_applyErrIs
  iapply applyErrIs_nil

/-- `Compact`'s outcome gives what the compactor tests of its error. -/
theorem errTreeOk_of_compactOutIs (E : apply.AEnv GF) (resp : Loc) (err : GoInterface) :
    compactOutIs (GF := GF) E resp err ⊢ v3compactor.errTreeOk err := by
  iintro H
  iunfold compactOutIs at H
  icases H with (⟨%Hok, -⟩ | ⟨-, Herr⟩)
  · rw [Hok.1]; iapply errTreeOk_nil
  · iapply errTreeOk_of_applyErrIs; iexact Herr

/-- **What a compactor's `Compact` call borrows and gives back** on the server `s`: the caller's
reader slots (the lead-time and logger mutexes', the auth store's, `E.RD`) and a reader token of
the store (`KV.Rev.contract`'s; the `lean` merge, R6, 2026-11-07: until then the store's
compaction-aware reader `mvcc.storeReaderC`). (R8, 2026-11-07: the call's thread token is not here
but the compactor goroutine's own, the one its `go` statement gives, which `v3compactor`'s
`revGetterOk`/`compactableOk` lend beside this; R6 had put one here, which no one could supply.) -/
def srvCompactR (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ srvLgReader s ∗ E.RD ∗ mvcc.api.mvccReaders E.γ 1)

/-- **A floor of the store's committed log is short** (`mvccState_reachable.law`'s bound at the
store invariant's state, which the floor is a prefix of). -/
theorem kvLogLb_len (Hp : mvcc.api.persistent.law (GF := GF))
    (Hr : mvcc.api.mvccState_reachable.law (GF := GF)) (kv : GoInterface) (γ : mvcc.api.MvccName)
    (Nx : mvcc.Log → IProp GF) (Cp : Int → IProp GF) [∀ l, Persistent (Nx l)]
    [∀ l, Timeless (Nx l)] [∀ c, Persistent (Cp c)] [∀ c, Timeless (Cp c)]
    (γs : srvApi.KVSNames) (L : mvcc.Log) :
    srvApi.kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢ srvApi.kvLogLb γs L ={⊤}=∗
      ⌜L.length + 3 ≤ 2 ^ 63⌝ := by
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := Hp.1 kv γ
  haveI := srvApi.kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk #HL
  iunfold srvApi.kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  ihave ⟨Hs, %Hf⟩ := srvApi.mvccState_facts Hr kv γ σ $$ [Hm Hs]
  · isplitl []
    · iexact Hm
    iexact Hs
  iunfold srvApi.kvLogLb at HL
  ihave %HL0 := mono_list_auth_lb_valid γs.slog 1 σ.log L $$ Hsl HL
  imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
  · inext
    iexists σ
    iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
  imodintro
  ipureintro
  have := HL0.2.length_le
  omega

/-- **The server is the compactor's `Compactable`** (review round 1, S3-3), for any permit `P`
that gives a positive revision the cluster's retention behind one the store has reached
(`srvRevLb`; periodic mode, 2026-11-02: the mode's permit, `compactableOk_server_mode`): from
`Compact.spec`, borrowing `srvCompactR`; (M2's apply side, item 15) at a server in compaction
mode, over the request path's view and the readers' at its names. -/
theorem compactableOk_server_of (hC : EtcdServer.Compact.spec (GF := GF) (hG := hG))
    (HpL : mvcc.api.persistent.law (GF := GF)) (HrL : mvcc.api.mvccState_reachable.law (GF := GF))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (P : Int → IProp GF)
    (hP : ∀ r, P r ⊢ ⌜0 < r⌝ ∗ srvRevLb E (r + E.cret)) (hcmp : E.cmp = true) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E ρ.rd ∗ idCred ρ.ids 1 ⊢
      v3compactor.compactableOk
        (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s) P (srvCompactR s E) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd, #Hcred⟩
  iunfold v3compactor.compactableOk
  iexists _
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %r %ctx %cd %p %Φ !> ⟨Hpm, HR, Htt, #Hctx, #Hspc, #Hlib, #Htr, Hreq⟩ HΦ
  ihave ⟨%Hr, #Hlb⟩ := hP r $$ Hpm
  iunfold srvCompactR at HR
  icases HR with ⟨Hlt, Hlr, Hrd, Hmr⟩
  ihave #Hkvi := srvKVInvs_of_read s E ρ.rd $$ Hsrd
  iunfold srvKVInvs at Hkvi
  icases Hkvi with ⟨#Hkv, -, #Hrl, #HkS, %Hm, %HNx, -⟩
  have Hcrt := Hm.2.1
  have Hwit := Hm.2.2.1
  haveI := Hwit.1
  haveI := Hwit.2.1
  haveI := Hwit.2.2.1
  haveI := Hwit.2.2.2
  -- (C3's server stage) at least the cluster's retention behind a revision reached
  ihave #Hlb' : srvRevLb E (r + ρ.rd.kv.cret) $$ []
  · iapply srvRevLb_mono E (r + ρ.rd.kv.cret) (r + E.cret) (by omega); iexact Hlb
  ihave #Hlb'' := Hlb'
  iunfold srvRevLb at Hlb''
  icases Hlb'' with ⟨%lg, #Hlgc, -, %Hlgl⟩
  imod kvLogLb_len HpL HrL E.kv E.γ E.Nx E.Cp E.γs lg $$ HkS Hlgc with %Hlgn
  have hfit : sint.Z (W64 (r + ρ.rd.kv.cret) : w64) = r + ρ.rd.kv.cret := by word
  -- (the client's `kv.Compact`, 2026-10-31) the store's certificate as the KV's revision reached
  -- (`kvRevLb_of_srvRevLb`, with the readers' view's invariants), at the request's revision
  iunfold compactReqIs at Hreq
  icases Hreq with ⟨%v, Hp, %Hv⟩
  ihave #Hlbv : srvRevLb E (sint.Z (W64 (r + ρ.rd.kv.cret) : w64)) $$ []
  · rw [hfit]; iexact Hlb'
  imod (kvRevLb_of_srvRevLb ρ.rd.raft ρ.rd.kv E HNx ⊤ (fun _ _ => CoPset.mem_full)
      (fun _ _ => CoPset.mem_full) (W64 (r + ρ.rd.kv.cret)))
    $$ Hkv Hrl Hlbv with #Hrev
  ihave #Hrev' : kvRevLbZ ρ.rd.kv (r + ρ.rd.kv.cret) $$ []
  · iapply kvRevLbZ_mono ρ.rd.kv (r + ρ.rd.kv.cret) (sint.Z (W64 (r + ρ.rd.kv.cret) : w64))
      (by omega)
    iunfold kvRevLb at Hrev; iexact Hrev
  -- (M2, the storage side, item 35) the permit's revision is past `0`: the scope premise
  iapply (hC s E ρ ctx cd p r (by omega)) $$ [Hlt Hlr Hrd Hmr Hp]
  · iframe Hlt Hlr Hrd Hmr; iframe #
    isplitr
    · ipureintro; exact hcmp
    iunfold compactReqIs
    iexists v
    iframe Hp
    ipureintro; exact Hv
  inext
  iintro %resp %err ⟨Hlt, Hlr, Hrd, Hmr, Hout⟩
  iapply HΦ
  iunfold srvCompactR
  iframe Hlt Hlr Hrd Hmr Htt
  iapply errTreeOk_of_compactOutIs; iexact Hout

/-- **The server is the revision compactor's `Compactable`**: its permit at a retention at least
the cluster's (`cret ≤ ret`, C3's server stage). -/
theorem compactableOk_server (hC : EtcdServer.Compact.spec (GF := GF) (hG := hG))
    (Hp : mvcc.api.persistent.law (GF := GF)) (Hr : mvcc.api.mvccState_reachable.law (GF := GF))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ret : Int) (hret : 0 ≤ ret) (hcmp : E.cmp = true)
    (hcr : (E.cret : Int) ≤ ret) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E ρ.rd ∗ idCred ρ.ids 1 ⊢
      v3compactor.compactableOk
        (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s)
        (v3compactor.revPermit (srvRevLb E) ret) (srvCompactR s E) := by
  refine compactableOk_server_of hC Hp Hr s E ρ _ (fun r => ?_) hcmp
  iintro H
  iunfold v3compactor.revPermit at H
  icases H with ⟨%Hr, #Hlb⟩
  isplitr
  · ipureintro; exact Hr
  iapply srvRevLb_mono E (r + E.cret) (r + ret) (by omega); iexact Hlb

/-- **The server is the periodic compactor's `Compactable`** (periodic mode, 2026-11-02): its
permit gives a revision the store had reached (`stampAt_elim`), so at a cluster retention of `0`
(a period is no revision count). -/
theorem compactableOk_server_periodic (hC : EtcdServer.Compact.spec (GF := GF) (hG := hG))
    (Hp : mvcc.api.persistent.law (GF := GF)) (Hr : mvcc.api.mvccState_reachable.law (GF := GF))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (period : Int) (γf : GName)
    (hcmp : E.cmp = true) (hcr : E.cret = 0) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E ρ.rd ∗ idCred ρ.ids 1 ⊢
      v3compactor.compactableOk
        (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s)
        (v3compactor.perPermit (srvRevLb E) period γf) (srvCompactR s E) := by
  refine compactableOk_server_of hC Hp Hr s E ρ _ (fun r => ?_) hcmp
  iintro H
  iunfold v3compactor.perPermit at H
  icases H with ⟨%Hr, %T, #Hst, -⟩
  ihave #Hlb := clockwork.stampAt_elim clockwork.realClock iprop(□ srvRevLb E r) T $$ Hst
  isplitr
  · ipureintro; exact Hr
  iapply srvRevLb_mono E (r + E.cret) r (by omega); iexact Hlb

/-- **The server is the compactor's `Compactable` in its mode** (periodic mode, 2026-11-02): the
mode's permit (`modePermit`), at a retention at least the cluster's in revision mode and at a
cluster retention of `0` in the other. -/
theorem compactableOk_server_mode (hC : EtcdServer.Compact.spec (GF := GF) (hG := hG))
    (Hp : mvcc.api.persistent.law (GF := GF)) (Hr : mvcc.api.mvccState_reachable.law (GF := GF))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (mode : GoString) (ret : Int) (γf : GName)
    (hcmp : E.cmp = true)
    (hcr : if mode = go!"revision" then 0 ≤ ret ∧ (E.cret : Int) ≤ ret else E.cret = 0) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E ρ.rd ∗ idCred ρ.ids 1 ⊢
      v3compactor.compactableOk
        (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s)
        (v3compactor.modePermit mode (srvRevLb E) ret γf) (srvCompactR s E) := by
  unfold v3compactor.modePermit
  split
  · next hm =>
    rw [ite_cond_eq_true _ _ (eq_true hm)] at hcr
    exact compactableOk_server hC Hp Hr s E ρ ret hcr.1 hcmp hcr.2
  · next hm =>
    rw [ite_cond_eq_false _ _ (eq_false hm)] at hcr
    exact compactableOk_server_periodic hC Hp Hr s E ρ ret γf hcmp hcr

/-- **The server's KV is the compactor's `RevGetter`** (M2, `NewServer.specCompact`): `s.kv.Rev()`
(`KV.Rev.contract` at the handle's dynamic type, at the store invariant's read update from the
bound's floor; the `lean` merge, R6, 2026-11-07: until then mvcc's internal `store.Rev`) reaches a
revision past every lower bound `srvRevLb` gave, and gives its own; it borrows `srvCompactR` (a
thread token and a reader token of the store). -/
theorem revGetterOk_server (Hp : mvcc.api.persistent.law (GF := GF))
    (Hr : mvcc.api.mvccState_reachable.law (GF := GF)) (hsh : mvcc.api.shapes.law (GF := GF))
    (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (kv : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      srvKVAddr s ↦□ kv ∗ isServerRead s E γr ⊢
      v3compactor.revGetterOk (srvRevLb E) kv (srvCompactR s E) := by
  haveI := Hp.1
  iintro ⟨#Pmv, #HkvA0, #Hsrd⟩
  ihave #Hkvi := srvKVInvs_of_read s E γr $$ Hsrd
  iunfold srvKVInvs at Hkvi
  icases Hkvi with ⟨-, -, -, #HkS, %Hm, -⟩
  have Hwit := Hm.2.2.1
  haveI := Hwit.1
  haveI := Hwit.2.1
  haveI := Hwit.2.2.1
  haveI := Hwit.2.2.2
  iunfold isServerRead at Hsrd
  icases Hsrd with ⟨%v, #Hf⟩
  iunfold srvReadFieldsAt at Hf
  icases Hf with ⟨-, -, #HkvA, #Hkv, %Hkveq0, -⟩
  ihave %Hkveq1 := typedPointsto_agree_wand _ _ _ _ _ $$ HkvA HkvA0
  subst Hkveq1
  ihave %Hsh := hsh.1 v.kv E.γ $$ Hkv
  obtain ⟨kty, kvv, Hkveq, -, -, hRevC, -⟩ := Hsh
  ihave #Hkv' : mvcc.api.isMvcc (interface.mkOk kty kvv) E.γ $$ []
  · rw [← Hkveq]; iexact Hkv
  iunfold v3compactor.revGetterOk
  rw [Hkveq]
  iexists _
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %n %Φ !> ⟨HR, Htt, #Hlb⟩ HΦ
  iunfold srvCompactR at HR
  icases HR with ⟨Hlt, Hlr, Hrd, Hmr⟩
  iunfold srvRevLb at Hlb
  icases Hlb with ⟨%log₀, #Hc0, -, %Hn⟩
  ihave HAU := srvApi.au_read (Nx := E.Nx) (Cp := E.Cp) Hp Hr E.kv E.γ E.γs log₀ $$ HkS Hc0
  wp_apply (hRevC E.γ (srvApi.kvReadAtG E.Nx E.Cp E.γs log₀)) $$ [Hmr HAU]
    as %rev ⟨Hmr, %σ, Hrdq, %Hrev⟩
  · iframe #; iframe Hmr
    iunfold srvApi.auRead at HAU
    iexact HAU
  iunfold srvApi.kvReadAtG at Hrdq
  icases Hrdq with ⟨%Hpre, #Hlc, #Hnx, -, -, %Hσ⟩
  have hle := Hpre.length_le
  have hst := (srvApi.reach_prefix σ Hσ.1).1
  have hlen2 : 2 ≤ σ.log.length := by
    have := hst.length_le; simpa [mvcc.api.mvccStart] using this
  have hz : sint.Z rev = (σ.log.length : Int) - 1 := by
    rw [Hrev, mvcc.api.MvccState.rev]
    have h3 := Hσ.2
    show sint.Z (W64 ((σ.log.length - 1 : Nat) : Int)) = _
    have : ((σ.log.length - 1 : Nat) : Int) = (σ.log.length : Int) - 1 := by omega
    rw [this]; word
  iapply HΦ
  iunfold srvCompactR
  iframe Hlt Hlr Hrd Hmr Htt
  isplitl
  · imodintro
    iunfold srvRevLb
    iexists σ.log
    iframe Hlc Hnx
    ipureintro; omega
  ipureintro; omega

end laws

end EtcdGrove
end Perennial
