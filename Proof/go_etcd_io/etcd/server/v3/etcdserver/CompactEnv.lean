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
  iintro H
  iunfold applyErrIs at H
  icases H with ⟨#Ht, -⟩
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

/-- **The server is the compactor's `Compactable`** (review round 1, S3-3): from `Compact.spec`,
for the revision compactor's permit over `srvRevLb` at a non-negative retention, borrowing
`srvCompactR`; (M2's apply side, item 15) at a server in compaction mode, over the request path's
view and the readers' at its names. -/
theorem compactableOk_server (hC : EtcdServer.Compact.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ret : Int) (hret : 0 ≤ ret) (hcmp : E.cmp = true) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E ρ.rd ∗ idCred ρ.ids 1 ⊢
      v3compactor.compactableOk
        (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s)
        (v3compactor.revPermit (srvRevLb E.γ) ret) (srvCompactR s E) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd, #Hcred⟩
  iunfold v3compactor.compactableOk
  iexists _
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %r %ctx %cd %p %Φ !> ⟨Hpm, HR, #Hctx, #Htr, Hreq⟩ HΦ
  iunfold v3compactor.revPermit at Hpm
  icases Hpm with ⟨%Hr, #Hlb⟩
  iunfold srvCompactR at HR
  icases HR with ⟨Hlt, Hlr, Hrd, Hst⟩
  ihave #Hlb' : srvRevLb E.γ r $$ []
  · iapply srvRevLb_mono E.γ r (r + ret) (by omega); iexact Hlb
  -- (M2, the storage side, item 35) the permit's revision is past `0`: the scope premise
  iapply (hC s E ρ ctx cd p r (by omega)) $$ [Hlt Hlr Hrd Hst Hreq]
  · iframe Hlt Hlr Hrd Hst Hreq; iframe #; ipureintro; exact hcmp
  inext
  iintro %resp %err ⟨Hlt, Hlr, Hrd, Hst, Hout⟩
  iapply HΦ
  iunfold srvCompactR
  iframe Hlt Hlr Hrd Hst
  iapply errTreeOk_of_compactOutIs; iexact Hout

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
