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
open mvcc.api (MvccName mvccLeases MvccState mvccDeleter)

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


/-- **The Revoke clause of the real lessor** (the lease-revoke plan's D3; strict M1, 2026-11-06:
over the restated `lessor.Revoke.spec`, mvcc's API): the lessor `lp` (its invariant at the store's
lessor names `mvccLeases γ`), and the rest resource `RO` lending, at the backend `B` its tie `BT`
names, the `Lease` bucket's part (`rbPart`, with the parameters' `leaseParams`) and the lessor's half
of `le.b`, given back at any buckets agreeing with `rs.bk` off `lease` (a revocation deletes only in
`lease`, keeping the bucket). The rest (the deleter, the backend share, the hook, the update) is the
clause's own premise, passed to `Revoke`. -/
theorem revokeClause_of_lessorInv (hRv : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    (lp : Loc) (γ : MvccName) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc)
    (BT : mvcc.KBReal → IProp GF) (RO : RestM → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      lease.lessorInv lp (mvccLeases γ) ∗
      □ (∀ (B : mvcc.KBReal) (rs : RestM), BT B -∗ RO rs -∗ BT B ∗
          backend.rbPart B.γB (· = mvcc.leaseName) rs.bk ∗ ⌜mvcc.leaseParams B.P⌝ ∗
          lease.lessorBeOn lp B.be ∗
          (∀ bk, ⌜∀ n, n ≠ mvcc.leaseName → bk.lookup n = rs.bk.lookup n⌝ -∗
            ⌜(rs.bk.lookup mvcc.leaseName).isSome → (bk.lookup mvcc.leaseName).isSome⌝ -∗
            backend.rbPart B.γB (· = mvcc.leaseName) bk ∗ lease.lessorBeOn lp B.be -∗
            RO { rs with bk := bk })) ⊢
      revokeClause ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty, #lp⟩ γ Pk f
        BT RO := by
  iintro ⟨#Hpkg, #Hmpkg, #Hinv, #Hlens⟩
  iunfold revokeClause
  iintro !> %id %σ₀ %L %rs %q %B %Pre %Q %Post %Y %Φ !>
    ⟨Htt, ⟨%rd, Hro, Hdel⟩, Hbk, Hhk, HBT, Hcs, %Hpure, Hau, Hown, Hrvk, #HK, HRO⟩ HΦ
  icases Hlens $$ %B %rs HBT HRO with ⟨HBT, Hrb, %hlp, Hbe, Hcl⟩
  iapply (hRv lp γ id rd q B (Pk B) f σ₀ L rs.bk Pre Q Post Y) $$
    [Htt Hro Hdel Hbk Hhk Hcs Hau Hown Hrvk Hrb Hbe]
  · iframe Hpkg Hmpkg Hinv Htt Hro Hdel Hbk Hhk Hcs Hau Hown Hrvk Hrb Hbe
    ipureintro; exact ⟨Hpure, hlp⟩
  iintro !> %err ⟨Htt, Hro, Hbk, Hbe, Hcase⟩
  icases Hcase with
    (⟨%Hnin, ⟨%e, #He, %Herr⟩, HPre, Hown, Hrvk, Hrb⟩ |
     ⟨%Hok, HY, HPost, Hown, Hrvk, Hrb⟩)
  · -- not live: nothing changed
    ihave %hD := leaseDels_notLive L σ₀.log id Hnin $$ HK
    iapply HΦ
    iframe Htt Hbk HBT
    isplitl [Hro Hdel]
    · iexists rd; iframe Hro Hdel
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
    iframe HPre Hown Hrvk HK
    iapply Hcl $$ %rs.bk %(fun _ _ => rfl) %(fun h => h) [$Hrb $Hbe]
  · -- live: the keys deleted, the record deleted
    obtain ⟨hid, rfl⟩ := Hok
    iapply HΦ
    iframe Htt Hbk HBT
    isplitl [Hro Hdel]
    · iexists rd; iframe Hro Hdel
    isplitr
    · iapply applyErrIs_nil
    iright
    isplitr
    · ipureintro; exact ⟨hid, rfl⟩
    iframe HY HPost Hown Hrvk
    isplitr
    · iapply leasesKnown_revoke L σ₀.log id $$ HK
    rw [show restRevoke id rs = { rs with bk := mvcc.rbDel rs.bk mvcc.leaseName (u64Le id).reverse }
      from rfl]
    iapply Hcl $$ %(mvcc.rbDel rs.bk mvcc.leaseName (u64Le id).reverse)
      %(fun n hn => by unfold mvcc.rbDel; rw [GMap.lookup_insert_ne _ _ (Ne.symm hn)])
      %(fun _ => by simp [mvcc.rbDel]) [$Hrb $Hbe]

/-- **The lessor's writes' resources, lent by the write right** (strict M1, 2026-11-06): at the
backend `B` its tie names, the write right `RW` splits into the lessor's backend contract's lent
resource `RW₁` (beside the backend's reader token: `lease.lessorBackend`'s `R`, which lends `le.b`),
with the backend contract at `B`'s batch lock and the hook `f`, and the `Lease` bucket's part
`Rb r`; `RW₁` and the bucket's part at `r` or after a put into `lease` give `RW` back. What a
`Grant` or `Checkpoint` takes and gives back. -/
def lessorWLens (lp : Loc) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc) (BT : mvcc.KBReal → IProp GF)
    (RW : IProp GF) : IProp GF :=
  iprop(□ (∀ B : mvcc.KBReal, BT B -∗ RW -∗ BT B ∗
    ∃ (RW₁ : IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
      (r : GMap GoString backend.BktData),
      lease.lessorBackend lp (Pk B) #f (bkWT B) iprop(bkRT B ∗ RW₁) Rb ∗ RW₁ ∗ Rb r ∗
      (∀ r', ⌜r' = r ∨ ∃ k v, r' = mvcc.rbSet r mvcc.leaseName k v⌝ -∗ RW₁ -∗ Rb r' -∗ RW)))

instance lessorWLens_persistent (lp : Loc) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc)
    (BT : mvcc.KBReal → IProp GF) (RW : IProp GF) : Persistent (lessorWLens lp Pk f BT RW) := by
  unfold lessorWLens; infer_instance

/-- **The apply package's lessor contract, of the real lessor** at `lp` (strict M1, 2026-11-06: over
mvcc's API, the store `γ`'s lessor names `mvccLeases γ`): its `isTxnLessor`, `Grant` and
`Checkpoint` from the proofs, the backend contract at each write's backend and the bucket's part lent
by the write right (`lessorWLens`), `Revoke` from its proof over the rest resource's lens
(`revokeClause_of_lessorInv`), `Lookup` given. -/
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
    (lp : Loc) (γ : MvccName) (Pk : mvcc.KBReal → IProp GF) (f : GoFunc)
    (BT : mvcc.KBReal → IProp GF) (RO : RestM → IProp GF) (RW : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      □ (∀ (B : mvcc.KBReal) (rs : RestM), BT B -∗ RO rs -∗ BT B ∗
          backend.rbPart B.γB (· = mvcc.leaseName) rs.bk ∗ ⌜mvcc.leaseParams B.P⌝ ∗
          lease.lessorBeOn lp B.be ∗
          (∀ bk, ⌜∀ n, n ≠ mvcc.leaseName → bk.lookup n = rs.bk.lookup n⌝ -∗
            ⌜(rs.bk.lookup mvcc.leaseName).isSome → (bk.lookup mvcc.leaseName).isSome⌝ -∗
            backend.rbPart B.γB (· = mvcc.leaseName) bk ∗ lease.lessorBeOn lp B.be -∗
            RO { rs with bk := bk })) ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lease.lessorInv lp (mvccLeases γ) ∗ lease.lessorCfg lp ∗ lessorWLens lp Pk f BT RW ∗
      □ (∀ id : w64,
        {{ True }} (App (Val (lp @!! go.GoType.PointerType lease.lessor.ty @!! go!"Lookup"))
          (Val #id))
        {{ (l : Loc), RET #l; ⌜l = null⌝ ∨ leaseIs l id }}) ⊢
      isApplyLessor (lease.lessorIface lp) γ Pk f BT RO RW := by
  iintro ⟨#Hmpkg, #Hlens, #Hpkg, #Hinv, #Hcfg, #HW, #HLookup⟩
  iunfold isApplyLessor
  isplitl []
  · iapply lease.isTxnLessor_of_lessorInv hGL hAt hDt hSRD hLk lp (mvccLeases γ) $$ [$Hpkg $Hinv]
  iexists (interface.mk (go.GoType.PointerType lease.lessor.ty) #lp)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %id %ttl %L %I %B %Pre %Q %Post %Φ !>
      ⟨Hcs, Hown, Hrvk, Hwt, Hrt, HBT, #Hgr, Hrw⟩ HΦ
    iunfold lessorWLens at HW
    icases HW $$ %B HBT Hrw with ⟨HBT, %RW₁, %Rb, %r, #Hlb, HRW₁, HRb, Hback⟩
    iapply (hGrant lp (mvccLeases γ) id ttl L I (Pk B) f (bkWT B) iprop(bkRT B ∗ RW₁) Rb r
      Pre Q Post) $$ [Hcs Hown Hrvk Hwt Hrt HRW₁ HRb]
    · iframe Hpkg Hinv Hcfg Hlb Hcs Hown Hrvk Hwt Hgr HRb
      iframe Hrt HRW₁
    iintro !> %l %err ⟨⟨Hrt, HRW₁⟩, (⟨%Hne, #Herr, Hown, Hrvk, HPre, HRb⟩ |
      ⟨%Hok, Hown, Hrvk, HPost, #HID, ⟨%mt, -, #Ht, HRb⟩⟩)⟩
    · iapply HΦ
      iframe Hrt HBT
      isplitl [HPre]
      · iright; iexact HPre
      isplitl [Hback HRW₁ HRb]
      · iapply Hback $$ %r %(Or.inl rfl) HRW₁ HRb
      isplitl [Hown Hrvk]
      · iexists L; iframe Hown Hrvk
        isplitr
        · ipureintro; intro x hx; exact hx
        ileft; ipureintro; exact Hne.1
      iapply lessorErrIs_applyErrIs err $$ [$Hpkg $Herr]
    · obtain ⟨Herr, Hln, -, -, Hnin⟩ := Hok
      subst Herr
      iapply HΦ
      iframe Hrt HBT
      isplitl [HPost]
      · ileft; iexact HPost
      isplitl [Hback HRW₁ HRb]
      · iapply Hback $$ %_ %(Or.inr ⟨_, _, rfl⟩) HRW₁ HRb
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
    iapply revokeClause_of_lessorInv hRv lp γ Pk f BT RO
    iframe Hpkg Hmpkg Hinv Hlens
  isplitr
  · iintro !> %id %rem %B %Pre %Q %Post %Φ !> ⟨Hcs, Hwt, Hrt, HBT, Hrw⟩ HΦ
    iunfold lessorWLens at HW
    icases HW $$ %B HBT Hrw with ⟨HBT, %RW₁, %Rb, %r, #Hlb, HRW₁, HRb, Hback⟩
    iapply (hCk lp (mvccLeases γ) id rem (Pk B) f (bkWT B) iprop(bkRT B ∗ RW₁) Rb r
      Pre Q Post) $$ [Hcs Hwt Hrt HRW₁ HRb]
    · iframe Hpkg Hinv Hcfg Hlb Hcs Hwt HRb
      iframe Hrt HRW₁
    iintro !> %err ⟨⟨Hrt, HRW₁⟩, %He, HPP⟩
    subst He
    iapply HΦ
    iframe Hrt HBT
    icases HPP with (⟨HPost, %t, HRb⟩ | ⟨HPre, HRb⟩)
    · isplitl [HPost]
      · ileft; iexact HPost
      isplitl [Hback HRW₁ HRb]
      · iapply Hback $$ %_ %(Or.inr ⟨_, _, rfl⟩) HRW₁ HRb
      iapply applyErrIs_nil
    · isplitl [HPre]
      · iright; iexact HPre
      isplitl [Hback HRW₁ HRb]
      · iapply Hback $$ %r %(Or.inl rfl) HRW₁ HRb
      iapply applyErrIs_nil
  · iexact HLookup

end proof

end apply
end EtcdGrove
end Perennial
