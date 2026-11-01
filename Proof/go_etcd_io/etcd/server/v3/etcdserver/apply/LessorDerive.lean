/-
The apply package's lessor contract (`apply.isApplyLessor`) of the real lessor, from the
lessor's proofs (2026-10-13, unit 9 of the backend). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean` and `LessorBackend.lean`.

`isApplyLessor_of_lessorInv`: the lessor at `lp` (`lease.lessorInv`, its configuration
`lease.lessorCfg`, its backend `lease.lessorBackend`, a contract on the backend's `Lease` bucket
under the batch lock) meets the contract's `isTxnLessor` (unit 8), `Grant`, `Checkpoint` and (the
lease-revoke plan, 2026-10-31) `Revoke` clauses (proved: `revokeClause_of_lessorInv`, with the
laws it rests on, `kvWriter_open`, `leasesKnown_revoke`, `leaseDels_notLive`); its `Lookup` clause
is the theorem's premise (stated as in the contract). The lessor's errors are the package's
`errors.New` variables (`lease.leaseErrVar`, the shape of `errVarLeaf`): `applyErrIs`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorContract
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Grant
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Checkpoint
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__TTL
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Revoke
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

/-- **No key on the lease, no deletion.** -/
theorem leaseDels_nil [GooseExts] (s : List EtcdKv) (id : w64) (h : ∀ v ∈ s, v.lease ≠ id) :
    mvcc.leaseDels s id = [] := by
  unfold mvcc.leaseDels mvcc.leaseDelKeys
  split
  · rfl
  · rw [List.filter_eq_nil_iff.2 (fun v hv => by simpa using h v hv)]; rfl

/-- After deleting the keys `ks`, a key-value is one of before, of a key not in `ks`. -/
theorem mem_applyDels [GooseExts] (r : w64) (ks : List GoString) :
    ∀ (s : List EtcdKv) (v : EtcdKv), v ∈ mvcc.applyChanges r s (ks.map mvcc.Change.del) →
      v ∈ s ∧ v.key ∉ ks := by
  induction ks with
  | nil => intro s v h; exact ⟨h, by simp⟩
  | cons k ks ih =>
    intro s v h
    have h' : mvcc.applyChanges r s ((k :: ks).map mvcc.Change.del) =
        mvcc.applyChanges r (mvcc.applyChange r s (.del k)) (ks.map mvcc.Change.del) := rfl
    rw [h'] at h
    obtain ⟨hv, hk⟩ := ih _ v h
    simp only [mvcc.applyChange, List.mem_filter] at hv
    obtain ⟨hv, hne⟩ := hv
    refine ⟨hv, ?_⟩
    simp only [List.mem_cons, not_or]
    exact ⟨by simpa using hne, hk⟩

/-- After the revocation of `id`, no key-value has lease `id` (unless `0`), and each was there. -/
theorem mem_revokeLog [GooseExts] (log : mvcc.Log) (id : w64) (v : EtcdKv)
    (h : v ∈ mvcc.stateAfter (revokeLog log id)) :
    v ∈ mvcc.stateAfter log ∧ (id ≠ W64 0 → v.lease ≠ id) := by
  unfold revokeLog at h
  rw [txn.stateAfter_commitLog] at h
  obtain ⟨hv, hk⟩ := mem_applyDels _ _ _ v h
  refine ⟨hv, fun h0 hl => hk ?_⟩
  unfold mvcc.leaseDelKeys
  rw [if_neg h0]
  exact List.mem_map.2 ⟨v, List.mem_filter.2 ⟨hv, by simp [hl]⟩, rfl⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- A lessor error is one `errors.Is` can take. -/
theorem lessorErrIs_applyErrIs (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lease.lessorErrIs err ⊢ applyErrIs err := by
  iintro ⟨#Hpkg, #Herr⟩
  ihave Hli : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hli with ⟨#Hnf, #Hex, #Htl, -⟩
  iunfold lease.lessorErrIs at Herr
  icases Herr with ⟨%g, %e, %Hg, #Hge, %He⟩
  ihave #Hv : errVarLeaf (GF := GF) g $$ []
  · rcases Hg with rfl | rfl | rfl
    · iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at Hnf
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact Hnf
    · iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at Hex
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact Hex
    · iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at Htl
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact Htl
  iapply errVar_applyErrIs g err $$ Hv
  iexists e; iframe Hge; ipureintro; exact He

/-- **Every lease of the state live after the revocation** (without `id`). -/
theorem leasesKnown_revoke (L : List w64) (log : mvcc.Log) (id : w64) :
    txn.leasesKnown (GF := GF) L (mvcc.stateAfter log) ⊢
      txn.leasesKnown (L.filter (· != id)) (mvcc.stateAfter (revokeLog log id)) := by
  iintro #HK
  iunfold txn.leasesKnown at HK
  iunfold txn.leasesOk at HK
  iunfold txn.leasesKnown
  iunfold txn.leasesOk
  iintro !> %l %hl
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hl
  obtain ⟨hv', hne⟩ := mem_revokeLog log id v hv
  ihave H := HK $$ %v.lease %(List.mem_map_of_mem hv')
  iunfold txn.leaseOk at H
  iunfold txn.leaseOk
  icases H with %H
  ipureintro
  rcases H with H | H
  · exact Or.inl H
  · by_cases h0 : v.lease = W64 0
    · exact Or.inl h0
    · right
      refine List.mem_filter.2 ⟨H, ?_⟩
      have : v.lease ≠ id := by
        intro e; exact hne (by rw [← e]; exact h0) e
      simpa using this

/-- **A lease not live has no key** (the state's leases are live or `0`). -/
theorem leaseDels_notLive (L : List w64) (log : mvcc.Log) (id : w64) (hid : id ∉ L) :
    txn.leasesKnown (GF := GF) L (mvcc.stateAfter log) ⊢
      ⌜mvcc.leaseDels (mvcc.stateAfter log) id = []⌝ := by
  iintro #HK
  by_cases hex : ∃ v ∈ mvcc.stateAfter log, v.lease = id
  · obtain ⟨v, hv, hvl⟩ := hex
    iunfold txn.leasesKnown at HK
    iunfold txn.leasesOk at HK
    ihave H := HK $$ %v.lease %(List.mem_map_of_mem hv)
    iunfold txn.leaseOk at H
    icases H with %H
    ipureintro
    rw [hvl] at H
    rcases H with H | H
    · unfold mvcc.leaseDels mvcc.leaseDelKeys; rw [if_pos H]; rfl
    · exact absurd H hid
  · ipureintro; exact leaseDels_nil _ _ (fun v hv h => hex ⟨v, hv, h⟩)


/-- **The Revoke clause of the real lessor** (the lease-revoke plan's D3): the lessor `lp` (its
invariant), its backend's write right lent by the rest resource (the tracked buckets and the
lessor's `le.b` half at the store's real backend; only the buckets change: a grant writes through
`RW`, a revocation through `RO`, the server's resource of the buckets at its model), the store
watchable (`kvWriter` then holds `watchWriter`'s parts) and its hook's facts. -/
theorem revokeClause_of_lessorInv (hRv : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    (lp s : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) (RO : RestM → IProp GF) :
    ⌜γ.watchQ = true⌝ ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      lease.lessorInv lp γ.leases ∗ mvcc.hookOk γ P f ∗
      □ (∀ rs : RestM, RO rs -∗ ∃ d : mvcc.KBReal, ⌜γ.kb = some d⌝ ∗
          mvcc.storeRb γ rs.bk ∗ lease.lessorBeOn lp d.be ∗
          (∀ bk, mvcc.storeRb γ bk ∗ lease.lessorBeOn lp d.be -∗ RO { rs with bk := bk })) ⊢
      revokeClause ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty, #lp⟩ s γ P f RO := by
  iintro ⟨%hw, #Hpkg, #Hmpkg, #Hinv, #Hhok, #Hlens⟩
  iunfold revokeClause
  iintro !> %id %log %L %rs %Pre %Q %Post %Φ !>
    ⟨Hcs, Hkw, Hsr, Hwt, %Hput, Hown, Hrvk, #HK, Hrd, HRO, #Hcert⟩ HΦ
  icases lease.rdAt_elim _ _ $$ Hrd with ⟨%rd, Hro, #Hrdc⟩
  icases (txn.kvWriter_open s γ log hw (fun ws γw => mvcc.rdIs rd ws s γw)) $$ [Hkw] with
    ⟨%ws, %γw, %Hγ, #Hrdi, Hww, Hfrag, Hclose⟩
  · iframe Hkw; iexact Hrdc
  obtain ⟨hγ, hsl, hch⟩ := Hγ
  subst hγ
  icases Hlens $$ HRO with ⟨%d, %hkb, Hrb, Hbe, Hcl⟩
  ihave Hhook : mvcc.hookIs γw.st P f $$ [Hfrag]
  · iapply (mvcc.hookIs_split γw.st P f).2; iframe Hhok Hfrag
  have hlen : (mvcc.stateAfter log).length ≤ 2 ^ 62 := by
    have hl : log.length ≤ 2 ^ 63 := by omega
    have hc : txn.logChanges log ≤ 2 ^ 62 := by
      unfold txn.logChanges; unfold mvcc.logCh at hch; omega
    have h := (txn.stateBound_stateAfter log hl hc).1
    unfold txn.logChanges at h; unfold mvcc.logCh at hch; omega
  iapply (hRv lp γw.st.leases id rd ws s γw log L d rs.bk P Pre Q Post f) $$
    [Hro Hsr Hwt Hww Hhook Hcs Hown Hrvk Hrb Hbe]
  · iframe Hro Hsr Hwt Hww Hhook Hcs Hown Hrvk Hrb Hbe Hpkg Hmpkg Hinv Hrdi Hcert
    isplitr
    · ipureintro; exact ⟨rfl, hkb⟩
    ipureintro; exact ⟨Hput, hlen⟩
  iintro !> %err ⟨Hro, Hsr, Hhook, Hbe, Hcase⟩
  icases (mvcc.hookIs_split γw.st P f).1 $$ Hhook with ⟨-, Hfrag⟩
  icases Hcase with
    (⟨%Hnin, ⟨%e, #He, %Herr⟩, Hwt, Hww, HPre, Hown, Hrvk, Hrb⟩ |
     ⟨%Hok, Hww, HPost, Hown, Hrvk, Hrb⟩)
  · -- not live: nothing changed
    ihave %hD := leaseDels_notLive L log id Hnin $$ HK
    iapply HΦ
    iframe Hsr
    isplitl [Hro]
    · iapply lease.rdAt_intro _ _ rd; iframe Hro; iexact Hrdc
    isplitr
    · iapply lessorErrIs_applyErrIs err $$ [$Hpkg]
      iunfold lease.lessorErrIs
      iexists go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound, e
      iframe He
      ipureintro; exact ⟨Or.inl rfl, Herr⟩
    ileft
    isplitr
    · ipureintro; exact ⟨Hnin, hD⟩
    isplitr
    · iexists e; iframe He; ipureintro; exact Herr
    iframe HPre Hwt Hown Hrvk HK
    isplitl [Hww Hfrag Hclose]
    · iapply Hclose $$ %log %hsl Hww Hfrag
    iapply Hcl $$ %rs.bk [$Hrb $Hbe]
  · -- live: the keys deleted, the record deleted
    obtain ⟨hid, rfl⟩ := Hok
    iapply HΦ
    iframe Hsr
    isplitl [Hro]
    · iapply lease.rdAt_intro _ _ rd; iframe Hro; iexact Hrdc
    isplitr
    · iapply applyErrIs_nil
    iright
    isplitr
    · ipureintro; exact ⟨hid, rfl⟩
    iframe HPost Hown Hrvk
    isplitl [Hww Hfrag Hclose]
    · iapply Hclose $$ %(revokeLog log id) %(txn.soleLog_commit log _ hsl) Hww Hfrag
    isplitr
    · iapply leasesKnown_revoke L log id $$ HK
    rw [show restRevoke id rs = { rs with bk := mvcc.rbDel rs.bk mvcc.leaseName (u64Le id).reverse }
      from rfl]
    iapply Hcl $$ %(mvcc.rbDel rs.bk mvcc.leaseName (u64Le id).reverse) [$Hrb $Hbe]


/-- **The apply package's lessor contract, of the real lessor** at `lp`, for a store whose lessor
ghost map is the lessor's: its `isTxnLessor`, `Grant` and `Checkpoint` from the proofs, its
`Revoke` and `Lookup` clauses (not yet proved of the real lessor) given. The lessor's backend
contract takes, per write, the write token `storeWT γ ∗ RW₀` and, for its put, the right `Rb r` to
the tracked buckets, both of which the write right `RW` holds (leases T3, L3c, 2026-10-27); the
contract's clauses do not state the put's effect yet (the apply layer's step, L3b). -/
theorem isApplyLessor_of_lessorInv
    (hGL : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (hAt : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (hDt : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (hSRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (hGrant : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (hCk : lease.lessor.Checkpoint.spec (GF := GF) (hG := hG))
    (hTTL : lease.Lease.TTL.spec (GF := GF) (hG := hG))
    (hRv : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    (lp s : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) (RO : RestM → IProp GF)
    (RW RW₀ : IProp GF) (Rb : GMap GoString backend.BktData → IProp GF) :
    ⌜γ.watchQ = true⌝ ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.hookOk γ P f ∗
      □ (∀ rs : RestM, RO rs -∗ ∃ d : mvcc.KBReal, ⌜γ.kb = some d⌝ ∗
          mvcc.storeRb γ rs.bk ∗ lease.lessorBeOn lp d.be ∗
          (∀ bk, mvcc.storeRb γ bk ∗ lease.lessorBeOn lp d.be -∗ RO { rs with bk := bk })) ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lease.lessorInv lp γ.leases ∗ lease.lessorCfg lp ∗
      lease.lessorBackend lp P f iprop(mvcc.storeWT γ ∗ RW₀) (mvcc.storeRT γ) Rb ∗
      □ (RW -∗ RW₀ ∗ ∃ r, Rb r) ∗
      □ (∀ id : w64,
        {{ True }} (App (Val (lp @!! go.GoType.PointerType lease.lessor.ty @!! go!"Lookup"))
          (Val #id))
        {{ (l : Loc), RET #l; ⌜l = null⌝ ∨ leaseIs l id }}) ⊢
      isApplyLessor (lease.lessorIface lp) s γ P f RO RW := by
  iintro ⟨%Hwq, #Hmpkg, #Hhok, #Hlens, #Hpkg, #Hinv, #Hcfg, #Hbe, #HRW, #HLookup⟩
  iunfold isApplyLessor
  isplitl []
  · iapply lease.isTxnLessor_of_lessorInv hGL hAt hDt hSRD hLk lp γ.leases $$ [$Hpkg $Hinv]
  iexists (interface.mk (go.GoType.PointerType lease.lessor.ty) #lp)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %id %ttl %L %I %Pre %Q %Post %Φ !> ⟨Hcs, Hown, Hrvk, Hwt, Hrt, #Hgr, Hrw⟩ HΦ
    icases HRW $$ Hrw with ⟨Hrw, %r, HRb⟩
    iapply (hGrant lp γ.leases id ttl L I P f iprop(mvcc.storeWT γ ∗ RW₀) (mvcc.storeRT γ) Rb r
      Pre Q Post) $$ [Hcs Hown Hrvk Hwt Hrt Hrw HRb]
    · iframe; iframe #
    iintro !> %l %err ⟨Hrt, (⟨%Hne, #Herr, Hown, Hrvk, HPre, -⟩ |
      ⟨%Hok, Hown, Hrvk, HPost, #HID, ⟨%mt, -, #Ht, -⟩⟩)⟩
    · iapply HΦ
      iframe Hrt
      isplitl [HPre]
      · iright; iexact HPre
      isplitl [Hown Hrvk]
      · iexists L; iframe Hown Hrvk
        isplitr
        · ipureintro; intro x hx; exact hx
        ileft; ipureintro; exact Hne.1
      iapply lessorErrIs_applyErrIs err $$ [$Hpkg $Herr]
    · obtain ⟨Herr, Hln, -, -, Hnin⟩ := Hok
      subst Herr
      iapply HΦ
      iframe Hrt
      isplitl [HPost]
      · ileft; iexact HPost
      isplitl [Hown Hrvk]
      · iexists (L ++ [id]); iframe Hown Hrvk
        isplitr
        · ipureintro; intro x hx; exact List.mem_append_left _ hx
        iright
        isplitr
        · ipureintro; rfl
        iexists id
        isplitl
        · iunfold leaseTTLIs
          iframe HID
          isplitr
          · ipureintro; exact Hln
          iintro !> %Φ' !> - HΦ'
          iapply (hTTL l _ DFrac.discard) $$ [$Hpkg $Ht]
          iintro !> -
          iapply HΦ'; itrivial
        ipureintro; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      iapply applyErrIs_nil
  isplitr
  · -- `Revoke` (the lease-revoke plan)
    iapply revokeClause_of_lessorInv hRv lp s γ P f RO
    iframe Hpkg Hmpkg Hinv Hhok Hlens
    ipureintro; exact Hwq
  isplitr
  · iintro !> %id %rem %Pre %Q %Post %Φ !> ⟨Hcs, Hwt, Hrt, Hrw⟩ HΦ
    icases HRW $$ Hrw with ⟨Hrw, %r, HRb⟩
    iapply (hCk lp γ.leases id rem P f iprop(mvcc.storeWT γ ∗ RW₀) (mvcc.storeRT γ) Rb r
      Pre Q Post) $$ [Hcs Hwt Hrt Hrw HRb]
    · iframe; iframe #
    iintro !> %err ⟨Hrt, %He, HPP⟩
    subst He
    iapply HΦ
    iframe Hrt
    isplitl [HPP]
    · icases HPP with (⟨HPost, -⟩ | ⟨HPre, -⟩)
      · ileft; iexact HPost
      · iright; iexact HPre
    iapply applyErrIs_nil
  · iexact HLookup

end proof

end apply
end EtcdGrove
end Perennial
