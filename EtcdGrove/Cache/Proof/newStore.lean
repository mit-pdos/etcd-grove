/-
Proof of `Spec/newStore.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.newStore
import EtcdGrove.Cache.Spec.btree_New
import EtcdGrove.Cache.Spec.kvItemLess
import EtcdGrove.Cache.Spec.newRingBuffer

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 k8s_io.utils.third_party.forked.golang

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

-- `wp_load` from a persistent struct points-to: the field-store `AccessStrict` instances
-- (which need `DFrac.own 1`) are found first and the search does not backtrack.
attribute [-instance] snapshot.snapshot_access_store_rev snapshot.snapshot_access_store_tree

/-- `rw.RLocker()` returns a (non-nil) `Locker` interface value.

**Perennial gap** (the one `sorry` of the store): `RWMutex.RLocker` is
`Locker((*rlocker)(rw))`, and Perennial's Go semantics has no rule for the conversion
`(*RWMutex) → (*rlocker)` (a conversion between pointer types with identical underlying
base types; `Golang/Defn` only converts pointers to and from `unsafe.Pointer`), so the
body is stuck after unfolding. `isStore` needs only `isCond c lk` for the result (the
`Cond`'s `Broadcast`); the `rlocker`'s `Lock`/`Unlock` (`isLocker`, for `Cond.Wait`) have
no spec either. -/
theorem newStore_RLocker [sync.Assumptions] (rw : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (rw @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"RLocker")) (Val #()))
    {{ (lk : GoInterfaceOk), RET #(GoInterface.ok lk); True }} := by
  sorry

theorem newStore.wp_proof
    (wp_btree_New : btree.New.spec (GF := GF) (hG := hG))
    (wp_kvItemLess : kvItemLess.spec (GF := GF) (hG := hG))
    (wp_newRingBuffer : newRingBuffer.spec (GF := GF) (hG := hG)) :
    newStore.spec (GF := GF) (hG := hG) := by
  intro degree cap
  wp_start as ⟨%Hdeg, %Hcap⟩
  wp_auto
  ihave Hless : btLessSpec (functions kvItemLess []) (kvItemIs (hG := hG)) kvLess $$ []
  · unfold btLessSpec
    iintro %a %b %va %vb
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply wp_kvItemLess a b va vb $$ [Hpre] HΦ'
    iframe
    iPkgInit
  wp_apply wp_btree_New kvItemPtrT degree (functions kvItemLess []) (kvItemIs (hG := hG)) kvLess
    $$ [Hless] as %t Ht
  · iframe; ipureintro; exact ⟨Hdeg, kvLess_swo⟩
  wp_apply wp_newRingBuffer (snapshot.ty.PointerType) cap _ (snapIs (hG := hG)) Prod.fst $$ []
    as %r Hr
  · isplitr
    · ipureintro; exact Hcap
    unfold revisionOfSpec
    iintro %p %h
    imodintro
    iintro %Φ' #Hp HΦ'
    unfold snapIs
    icases Hp with ⟨%t', #Hpt, -⟩
    wp_auto
    iapply HΦ'
    itrivial
  iNamed Hr
  wp_auto
  iStructNamed «$r0»
  iStructNamedPrefix latest "L"
  ipersist degree
  have Hok' : RingOk rb (sint.nat cap) ([] : List (w64 × KvMap)).length := Hok
  ihave Hhist := ownRingBuffer_intro (storeHistAddr «$r0_ptr») (sint.nat cap) (snapIs (hG := hG))
    Prod.fst [] rb ents Hok' Hrev Hsorted $$ history Hbuf Hitems HrevOf
  iclear Hr
  imod ghostVar_alloc (GF := GF) StoreState.init with ⟨%γs, Hgs⟩
  icases ghostVar_split γs StoreState.init (1 : Qp).half (1 : Qp).half $$ [Hgs] with ⟨Hgs1, Hgs2⟩
  · rw [Qp.half_add_half]; iexact Hgs
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γr, Hauth, #Hlb⟩
  have Hinv0 : StoreInv (sint.nat cap) StoreState.init := by
    constructor <;> simp [StoreState.init, RevSorted] <;> first | word | skip
  imod sync.init_RWMutex (storeLockInv (hG := hG) «$r0_ptr» ⟨γs, γr⟩ (sint.nat cap))
    (storeMuAddr «$r0_ptr») $$ [Hgs1 Hauth Lrev Hhist] mu with Htoks
  · inext
    unfold storeLockInv
    iexists StoreState.init
    simp only [named]
    iframe
    ipureintro; exact Hinv0
  iapply wp_fupd
  wp_apply newStore_RLocker as %lk _
  wp_apply sync.wp_NewCond as %c #Hcond
  ipersist revCond
  obtain ⟨n, hn⟩ : ∃ n, sync.rwmutex.actualMaxReaders.toNat = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by have := sync.actualMaxReaders_pos; omega)).symm⟩
  rw [hn, List.replicate_succ, Nat.add_sub_cancel]
  icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Hw, Hrd⟩
  imodintro
  iapply HΦ $$ %«$r0_ptr» %(StoreNames.mk γs γr)
  isplitr
  · unfold isStore
    iexists c, lk, degree
    simp only [named]
    iframe #
    ipureintro
    refine ⟨Hdeg, ?_, ?_⟩ <;> word
  isplitl [Hgs2 Hw Ltree Ht]
  · unfold storeWriter storeLatestTree
    iframe Hgs2 Hw
    isplitl
    · iexists t
      iframe
      unfold kvsAt
      imodintro
      iintro %e %He
      exact absurd He List.not_mem_nil
    isplitr
    · unfold storeRevLb
      rw [show sint.nat StoreState.init.latestRev = 0 from rfl]
      iexact Hlb
    ipureintro; exact Hinv0
  isplitr
  · unfold storeRevLb
    rw [show sint.nat (W64 0) = 0 from rfl]
    iexact Hlb
  unfold storeReader
  iexact Hrd

end proof

end EtcdGrove
end Perennial
