/-
**The auto-compactor's environment on the server** (M2, `notes/m2-plan.md`, S4; review round 1,
S3-3): the laws that make the server what the frozen compactor contracts take, so that
`EtcdServer.Compact.spec` is checked against `v3compactor.compactableOk`:

* `errTreeOk_of_applyErrIs`, `errTreeOk_nil`: an error the request path reports, or `nil`, is one
  the compactor's `errors.Is(err, ErrCompacted)` can test (`v3compactor.errTreeOk`);
* `compactableOk_server`: the server is a `Compactable` for the compactor's revision permit over
  `srvRevLb` (a permit's `□ RevLb (r + ret)` gives `r` reached, what `Compact.spec` takes), with the
  resource every call gives back (the caller's reader slots and the store's reader);
* `revGetterOk_server`: the server's KV (`s.kv`) is the compactor's `RevGetter` over `srvRevLb`
  (`mvcc.store.Rev.spec`), borrowing the same resource.

Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Compact
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Rev
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.KVView
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite

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
reader slots (the lead-time and logger mutexes', the auth store's, `E.RD`) and the store's reader. -/
def srvCompactR (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ srvLgReader s ∗ E.RD ∗ mvcc.storeReaderC E.s E.γ)

/-- **The server is the compactor's `Compactable`** (review round 1, S3-3), for any permit `P`
that gives a positive revision the cluster's retention behind one the store has reached
(`srvRevLb`; periodic mode, 2026-11-02: the mode's permit, `compactableOk_server_mode`): from
`Compact.spec`, borrowing `srvCompactR`; (M2's apply side, item 15) at a server in compaction
mode, over the request path's view and the readers' at its names. -/
theorem compactableOk_server_of (hC : EtcdServer.Compact.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (P : Int → IProp GF)
    (hP : ∀ r, P r ⊢ ⌜0 < r⌝ ∗ srvRevLb E.γ (r + E.cret)) (hcmp : E.cmp = true) :
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
  iintro %r %ctx %cd %p %Φ !> ⟨Hpm, HR, #Hctx, #Htr, Hreq⟩ HΦ
  ihave ⟨%Hr, #Hlb⟩ := hP r $$ Hpm
  iunfold srvCompactR at HR
  icases HR with ⟨Hlt, Hlr, Hrd, Hst⟩
  ihave #Hkvi := srvKVInvs_of_read s E ρ.rd $$ Hsrd
  iunfold srvKVInvs at Hkvi
  icases Hkvi with ⟨#Hkv, #Hci, #Hrl, %Hcok, -, %Hcrt, -⟩
  -- (C3's server stage) at least the cluster's retention behind a revision reached
  ihave #Hlb' : srvRevLb E.γ (r + ρ.rd.kv.cret) $$ []
  · iapply srvRevLb_mono E.γ (r + ρ.rd.kv.cret) (r + E.cret) (by omega); iexact Hlb
  ihave #Hlb'' := Hlb'
  iunfold srvRevLb at Hlb''
  icases Hlb'' with ⟨%lg, #Hlgc, -, %Hlgl⟩
  ihave %Hlgn := idxCert_len E.γ.idx lg $$ Hlgc
  have hfit : sint.Z (W64 (r + ρ.rd.kv.cret) : w64) = r + ρ.rd.kv.cret := by word
  -- (the client's `kv.Compact`, 2026-10-31) the store's certificate as the KV's revision reached
  -- (`kvRevLb_of_srvRevLb`, with the readers' view's invariants), at the request's revision
  iunfold compactReqIs at Hreq
  icases Hreq with ⟨%v, Hp, %Hv⟩
  ihave #Hlbv : srvRevLb E.γ (sint.Z (W64 (r + ρ.rd.kv.cret) : w64)) $$ []
  · rw [hfit]; iexact Hlb'
  imod (kvRevLb_of_srvRevLb ρ.rd.raft ρ.rd.kv E.γ Hcok ⊤ (fun _ _ => CoPset.mem_full)
      (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full) (W64 (r + ρ.rd.kv.cret)))
    $$ Hkv Hci Hrl Hlbv with #Hrev
  ihave #Hrev' : kvRevLbZ ρ.rd.kv (r + ρ.rd.kv.cret) $$ []
  · iapply kvRevLbZ_mono ρ.rd.kv (r + ρ.rd.kv.cret) (sint.Z (W64 (r + ρ.rd.kv.cret) : w64))
      (by omega)
    iunfold kvRevLb at Hrev; iexact Hrev
  -- (M2, the storage side, item 35) the permit's revision is past `0`: the scope premise
  iapply (hC s E ρ ctx cd p r (by omega)) $$ [Hlt Hlr Hrd Hst Hp]
  · iframe Hlt Hlr Hrd Hst; iframe #
    isplitr
    · ipureintro; exact hcmp
    iunfold compactReqIs
    iexists v
    iframe Hp
    ipureintro; exact Hv
  inext
  iintro %resp %err ⟨Hlt, Hlr, Hrd, Hst, Hout⟩
  iapply HΦ
  iunfold srvCompactR
  iframe Hlt Hlr Hrd Hst
  iapply errTreeOk_of_compactOutIs; iexact Hout

/-- **The server is the revision compactor's `Compactable`**: its permit at a retention at least
the cluster's (`cret ≤ ret`, C3's server stage). -/
theorem compactableOk_server (hC : EtcdServer.Compact.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ret : Int) (hret : 0 ≤ ret) (hcmp : E.cmp = true)
    (hcr : (E.cret : Int) ≤ ret) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E ρ.rd ∗ idCred ρ.ids 1 ⊢
      v3compactor.compactableOk
        (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s)
        (v3compactor.revPermit (srvRevLb E.γ) ret) (srvCompactR s E) := by
  refine compactableOk_server_of hC s E ρ _ (fun r => ?_) hcmp
  iintro H
  iunfold v3compactor.revPermit at H
  icases H with ⟨%Hr, #Hlb⟩
  isplitr
  · ipureintro; exact Hr
  iapply srvRevLb_mono E.γ (r + E.cret) (r + ret) (by omega); iexact Hlb

/-- **The server is the periodic compactor's `Compactable`** (periodic mode, 2026-11-02): its
permit gives a revision the store had reached (`stampAt_elim`), so at a cluster retention of `0`
(a period is no revision count). -/
theorem compactableOk_server_periodic (hC : EtcdServer.Compact.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (period : Int) (γf : GName)
    (hcmp : E.cmp = true) (hcr : E.cret = 0) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E ρ.rd ∗ idCred ρ.ids 1 ⊢
      v3compactor.compactableOk
        (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s)
        (v3compactor.perPermit (srvRevLb E.γ) period γf) (srvCompactR s E) := by
  refine compactableOk_server_of hC s E ρ _ (fun r => ?_) hcmp
  iintro H
  iunfold v3compactor.perPermit at H
  icases H with ⟨%Hr, %T, #Hst, -⟩
  ihave #Hlb := clockwork.stampAt_elim clockwork.realClock iprop(□ srvRevLb E.γ r) T $$ Hst
  isplitr
  · ipureintro; exact Hr
  iapply srvRevLb_mono E.γ (r + E.cret) r (by omega); iexact Hlb

/-- **The server is the compactor's `Compactable` in its mode** (periodic mode, 2026-11-02): the
mode's permit (`modePermit`), at a retention at least the cluster's in revision mode and at a
cluster retention of `0` in the other. -/
theorem compactableOk_server_mode (hC : EtcdServer.Compact.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (mode : GoString) (ret : Int) (γf : GName)
    (hcmp : E.cmp = true)
    (hcr : if mode = go!"revision" then 0 ≤ ret ∧ (E.cret : Int) ≤ ret else E.cret = 0) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E ρ.rd ∗ idCred ρ.ids 1 ⊢
      v3compactor.compactableOk
        (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s)
        (v3compactor.modePermit mode (srvRevLb E.γ) ret γf) (srvCompactR s E) := by
  unfold v3compactor.modePermit
  split
  · next hm =>
    rw [ite_cond_eq_true _ _ (eq_true hm)] at hcr
    exact compactableOk_server hC s E ρ ret hcr.1 hcmp hcr.2
  · next hm =>
    rw [ite_cond_eq_false _ _ (eq_false hm)] at hcr
    exact compactableOk_server_periodic hC s E ρ ret γf hcmp hcr

/-- **The server's KV is the compactor's `RevGetter`** (M2, `NewServer.specCompact`): `s.kv.Rev()`
(`mvcc.store.Rev.spec`, through the watchable store) reaches a revision past every lower bound
`srvRevLb` gave, and gives its own; it borrows `srvCompactR` (the store's reader). -/
theorem revGetterOk_server (hRev : mvcc.store.Rev.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (kv : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      srvKVAddr s ↦□ kv ∗ isServerRead s E γr ⊢
      v3compactor.revGetterOk (srvRevLb E.γ) kv (srvCompactR s E) := by
  iintro ⟨#Pmv, #HkvA0, #Hsrd⟩
  iunfold isServerRead at Hsrd
  icases Hsrd with ⟨%v, #Hf⟩
  iunfold srvReadFieldsAt at Hf
  icases Hf with ⟨-, -, #HkvA, #Hkv, #HrvA, #Hrv, -⟩
  ihave %Hkveq0 := typedPointsto_agree_wand _ _ _ _ _ $$ HkvA HkvA0
  subst Hkveq0
  ihave %Hkvok := txn.isKV_ok _ E.s E.γ $$ Hkv
  obtain ⟨kty, kvv, Hkveq⟩ := Hkvok
  ihave ⟨#Hko0, -⟩ := txn.isKV_kvOver _ E.s E.γ $$ Hkv
  ihave #Hko : mvcc.kvOver (interface.mkOk kty kvv) E.s $$ []
  · rw [← Hkveq]; iexact Hko0
  iunfold v3compactor.revGetterOk
  rw [Hkveq]
  iexists _
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %n %Φ !> ⟨HR, #Hlb⟩ HΦ
  iunfold srvCompactR at HR
  icases HR with ⟨Hlt, Hlr, Hrd, Hrdr⟩
  iunfold srvRevLb at Hlb
  icases Hlb with ⟨%log₀, #Hc0, -, %Hn⟩
  imod ownToks_0 (GF := GF) E.γ.revs with Hnone
  iapply mvcc.kvOver_rev_wp kty kvv E.s
  iframe Hko
  wp_apply hRev E.s v.rv E.γ 0 log₀ $$ [Hrdr Hnone] as %rev ⟨Hrdr, -, %log, #Hlc, #Hcok, %Hl⟩
  · iframe #; iframe
  obtain ⟨Hpre, Hlen, Hne, Hrev⟩ := Hl
  have hpos : 0 < log.length := List.length_pos_iff.mpr Hne
  have hle := Hpre.length_le
  have hz : sint.Z rev = (log.length : Int) - 1 := by subst Hrev; word
  iapply HΦ
  iunfold srvCompactR
  iframe Hlt Hlr Hrd Hrdr
  isplitl
  · imodintro
    iunfold srvRevLb
    iexists log
    iframe Hlc Hcok
    ipureintro; omega
  ipureintro; omega

end laws

end EtcdGrove
end Perennial
