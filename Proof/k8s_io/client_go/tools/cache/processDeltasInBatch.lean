/-
Proof of `Spec/k8s_io/client_go/tools/cache/processDeltasInBatch.lean`. Lean-first.

The loop over the deltas keeps the writes `txns` (`batchTxs`), the callbacks (each a closure over
its iteration's `old` and `obj`, made read-only: `cbOk`, the event `batchEvs` gives it), and
`inBatch` (the key's object after the deltas so far, `nil` for a deletion; a key it lacks is the
store's, read through the exclusive writer at `σ`). Then `Transaction` (the store's one step, by
the writer), then the callbacks in order.
-/
module

public import Spec.k8s_io.client_go.tools.cache.processDeltasInBatch
public import Spec.k8s_io.client_go.tools.cache.cache__GetByKey
public import Spec.k8s_io.client_go.tools.cache.cache__Transaction
public import Spec.errors.Join

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section model
variable [FfiSyntax] [GoGlobalContext]

/-- The Go delta of an object delta. -/
def FD.toDelta : FD → Delta
  | .obj t o => Delta.mk t o
  | _ => Delta.mk go!"" interface.nil

/-- `inBatch` after a delta: the key's object (`nil` for a deletion). -/
theorem inBatch_step (KF : GoInterface → GoString) (it0 : Items) (pre : List FD)
    (M : GMap GoString GoInterface) (t : GoString) (o x : GoInterface)
    (hx : x = if t = go!"Deleted" then interface.nil else o)
    (HM : ∀ k, objAt (pre.foldl (fdItems KF) it0) k = (M !! k).getD (objAt it0 k)) :
    ∀ k, objAt ((pre ++ [FD.obj t o]).foldl (fdItems KF) it0) k =
      ((<[KF o := x]> M) !! k).getD (objAt it0 k) := by
  intro k
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have := HM k
  generalize pre.foldl (fdItems KF) it0 = cur at this
  unfold fdItems
  rw [GMap.lookup_insert_eq_iff]
  by_cases ht : t = go!"Deleted"
  · simp only [ht, ↓reduceIte] at hx ⊢
    subst hx
    unfold objAt
    by_cases hk : KF o = k
    · subst hk; simp
    · simp only [hk, ↓reduceIte, GMap.lookup_delete_iff]; unfold objAt at this; exact this
  · simp only [ht, ↓reduceIte] at hx ⊢
    rw [hx]
    unfold objAt
    by_cases hk : KF o = k
    · subst hk; simp
    · simp only [hk, ↓reduceIte, GMap.lookup_insert_eq_iff]; unfold objAt at this; exact this

theorem inBatch_vals (KF : GoInterface → GoString) (os : List GoInterface)
    (M : GMap GoString GoInterface) (o x : GoInterface) (ho : o ∈ os)
    (hx : x = interface.nil ∨ x = o)
    (HMv : ∀ k y, M !! k = some y → y = interface.nil ∨ y ∈ os) :
    ∀ k y, (<[KF o := x]> M) !! k = some y → y = interface.nil ∨ y ∈ os := by
  intro k y hy
  rw [GMap.lookup_insert_eq_iff] at hy
  split at hy
  · cases hy; rcases hx with rfl | rfl
    · left; rfl
    · right; exact ho
  · exact HMv k y hy

end model

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- Object deltas' Go deltas are their `toDelta`s, their objects meeting `OK`. -/
theorem fdAt_objs (OK : GoInterface → IProp GF) :
    ∀ (ds : List FD) (vs : List Delta), (∀ d ∈ ds, ∃ t o, d = .obj t o) →
      ([∗list] d;v ∈ ds;vs, fdAt OK d v) ⊢ ⌜vs = ds.map FD.toDelta⌝ ∗ □ [∗list] d ∈ ds, OK d.obj?
  | [], vs, _ => by
    iintro H
    ihave %h := BigSepL2.bigSepL2_nil_inv_left $$ H
    subst h
    isplitr
    · ipureintro; rfl
    imodintro; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  | d :: ds, vs, h => by
    obtain ⟨t, o, rfl⟩ := h _ List.mem_cons_self
    iintro H
    ihave H := (BigSepL2.bigSepL2_cons_inv_left (Φ := fun _ d v => fdAt OK d v)).1 $$ H
    icases H with ⟨%v, %vs', %hv, Hd, Hrest⟩
    subst hv
    ihave ⟨%hr, #Hr⟩ := fdAt_objs OK ds vs' (fun d hd => h d (List.mem_cons_of_mem _ hd)) $$ Hrest
    iunfold fdAt at Hd
    icases Hd with ⟨%Hv, #Ho⟩
    isplitr
    · ipureintro; rw [Hv.1, hr]; rfl
    imodintro
    iapply (BigSepL.bigSepL_cons (Φ := fun _ (d : FD) => OK d.obj?)).2
    rw [show (FD.obj t o).obj? = o from rfl]
    isplitl
    · iexact Ho
    · iexact Hr

/-- **A callback's contract**: it delivers the event `e`. -/
def cbOk (H : List Ev → IProp GF) (f : GoFunc) (e : Ev) : IProp GF :=
  iprop(∀ evs : List Ev, {{ H evs }} (App (Val #f) (Val #())) {{ RET #(); H (evs ++ [e]) }})

instance cbOk_persistent (H : List Ev → IProp GF) (f : GoFunc) (e : Ev) :
    Persistent (cbOk H f e) := by
  unfold cbOk; infer_instance

theorem processDeltasInBatch.wp_proof
    (wp_GetByKey : cache.GetByKey.spec (GF := GF) (hG := hG))
    (wp_Txn : cache.Transaction.spec (GF := GF) (hG := hG))
    (wp_Join : errors.Join.spec (GF := GF) (hG := hG)) :
    processDeltasInBatch.spec (GF := GF) (hG := hG) := by
  intro lg h ca ts γ OK Fam kf kf' KF rvOf SW Rw σ H evs ds vs sl b hty
  have hty' := hty
  obtain ⟨-, hcs, -⟩ := hty'
  wp_start as ⟨#Hca, Hr, #Hsw, HSW, %HRw, #Hh, HH, Hds, Hsl, %Hobj, #Hkey, #Hkey', #Hacc⟩
  have Hobj' : ∀ d ∈ ds, ∃ t o, d = .obj t o := fun d hd => (Hobj d hd).1
  ihave ⟨%Hvs, #Hoks⟩ := fdAt_objs OK ds vs Hobj' $$ Hds
  subst Hvs
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := Transaction) (W64 0)) as %ts0 ⟨Hts0, Htcap0⟩
  · ipureintro; word
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := GoFunc) (W64 0)) as %cs0 ⟨Hcs0, Hccap0⟩
  · ipureintro; word
  (try wp_auto)
  simp only [hcs, ↓reduceIte]
  (try wp_auto)
  wp_apply (wp_map_make2 (K := GoString) (V := GoInterface) _ go.string (go.GoType.InterfaceType []))
    as %m Hm
  (try wp_auto)
  ipersist handler
  ipersist isInInitialList
  ipersist keyFunc
  ipersist clientState
  iunfold handlerOk at Hh
  icases Hh with ⟨%hi, %hh, #HonAdd, #HonUpd, #HonDel⟩
  subst hh
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (n : w64) (dv : Delta) (tsl csl : GoSlice) (fs : List GoFunc)
      (M : GMap GoString GoInterface),
      "i" ∷ i_ptr ↦ n ∗ "d" ∷ d_ptr ↦ dv ∗
      "txns" ∷ txns_ptr ↦ tsl ∗
      "Htsl" ∷ tsl ↦* ((batchTxs KF σ.items (ds.take (sint.nat n))).map Tx.txn) ∗
      "Htcap" ∷ ownSliceCap Transaction tsl (DFrac.own 1) ∗
      "callbacks" ∷ callbacks_ptr ↦ csl ∗ "Hcsl" ∷ csl ↦* fs ∗
      "Hccap" ∷ ownSliceCap GoFunc csl (DFrac.own 1) ∗
      "#Hcbs" ∷ □ ([∗list] f;e ∈ fs;batchEvs KF b σ.items (ds.take (sint.nat n)), cbOk H f e) ∗
      "Hm" ∷ m ↦$ M ∗
      "%HM" ∷ ⌜∀ k, objAt ((ds.take (sint.nat n)).foldl (fdItems KF) σ.items) k =
        (M !! k).getD (objAt σ.items k)⌝ ∗
      "%HMv" ∷ ⌜∀ k x, M !! k = some x → x = interface.nil ∨ x ∈ ds.map FD.obj?⌝ ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝) $$ [i d txns Hts0 Htcap0 callbacks Hcs0 Hccap0 Hm]
  · iexists W64 0, _, ts0, cs0, [], ∅
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.foldl_nil, batchTxs,
      batchEvs, List.map_nil]
    iframe
    isplitr
    · imodintro; iapply BigSepL2.bigSepL2_nil.2; iempintro
    ipureintro
    simp only [GMap.lookup_empty, reduceCtorEq, false_implies, implies_true, true_and,
      Option.getD_none]
    word
  wp_for IH
  iunfold keyOk at Hkey'
  wp_if_destruct
  · have Hlt : sint.nat n < ds.length := by
      have := Hlen.1; simp only [List.length_map] at this; word
    obtain ⟨d0, Hd0⟩ : ∃ d0, ds[sint.nat n]? = some d0 := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨⟨t, o, rfl⟩, hkind⟩ := Hobj _ (List.mem_of_getElem? Hd0)
    have Hidx : (ds.map FD.toDelta)[(sint.Z n).toNat]? = some (Delta.mk t o) := by
      rw [show (sint.Z n).toNat = sint.nat n by word, List.getElem?_map, Hd0]; rfl
    have hoin : o ∈ ds.map FD.obj? := List.mem_map.2 ⟨_, List.mem_of_getElem? Hd0, rfl⟩
    ihave #HOKo := BigSepL.bigSepL_lookup (Φ := fun _ (d : FD) => iprop(OK d.obj?)) Hd0 $$ Hoks
    rw [show (FD.obj t o).obj? = o from rfl]
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have htake : ds.take (sint.nat (n + W64 1)) = ds.take (sint.nat n) ++ [FD.obj t o] := by
      rw [hn1, List.take_add_one, Hd0]; rfl
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) (ds.map FD.toDelta) (DFrac.own 1) (Delta.mk t o) Hn.1
      $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hidx
    (try wp_auto)
    wp_apply Hkey' $$ []
    · imodintro; ipureintro; exact hoin
    iintro %k %err %hk
    obtain ⟨rfl, rfl⟩ := hk
    (try wp_auto)
    simp only [FD.kindOk] at hkind
    by_cases ht : t = go!"Deleted"
    · subst ht
      rw [decide_eq_false (by simp)]
      (try wp_auto)
      wp_apply (wp_mapInsert go.string m M (KF o) GoInterface.nil) $$ [$Hm] as Hm
      (try wp_auto)
      ipersist obj
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %l1 ⟨Hl1, -⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Htsl $Htcap $Hl1] as %tsl' ⟨Htsl, Htcap, -⟩
      (try wp_auto)
      wp_func_lits
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %l2 ⟨Hl2, -⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hcsl $Hccap $Hl2] as %csl' ⟨Hcsl, Hccap, -⟩
      (try wp_auto)
      wp_for_post
      have htx : (batchTxs KF σ.items (ds.take (sint.nat n) ++ [FD.obj go!"Deleted" o])).map Tx.txn =
          (batchTxs KF σ.items (ds.take (sint.nat n))).map Tx.txn ++
            [Transaction.mk o go!"Delete"] := by
        rw [batchTxs_snoc, List.map_append]; simp [fdTx, Tx.txn]
      have hev : batchEvs KF b σ.items (ds.take (sint.nat n) ++ [FD.obj go!"Deleted" o]) =
          batchEvs KF b σ.items (ds.take (sint.nat n)) ++ [Ev.delete o] := by
        rw [batchEvs_snoc]; simp [fdEv]
      iframe
      iexists n + W64 1, _, tsl', csl', _, <[KF o := GoInterface.nil]> M
      rw [htake, htx, hev]
      iframe
      isplitr
      · imodintro
        iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ f e => cbOk H f e)).2
        isplitl
        · iexact Hcbs
        iunfold cbOk
        iintro %evs' %Φ' !> HH' HΦ'
        wp_pures
        (try wp_auto)
        ihave #HD := HonDel $$ %evs' %o
        wp_bind (App (Val #(methods hi.ty go!"OnDelete" hi.v)) _)
        iapply HD $$ [$HH']
        · iunfold delOk; ileft; iexact HOKo
        inext
        iintro HH'
        (try wp_auto)
        iapply HΦ'; iexact HH'
      ipureintro
      refine ⟨inBatch_step KF σ.items _ M _ o GoInterface.nil (by simp) HM,
        inBatch_vals KF _ M o GoInterface.nil hoin (Or.inl rfl) HMv, by word⟩
    · rcases hkind with ht' | ht' | ht'
      · rw [ht']
        rw [decide_eq_false (by simp)]
        (try wp_auto)
        rw [← ht']
        wp_apply (wp_map_lookup2 go.string (go.GoType.InterfaceType []) m M (KF o) (DFrac.own 1))
          $$ [$Hm] as Hm
        rcases hMk : M !! KF o with _ | x
        · simp only [Option.isSome_none, Option.getD_none]
          (try wp_auto)
          wp_bind
          iapply (wp_GetByKey ca ts γ OK Fam kf (KF o)) $$ [$Hpkg $Hca $Hr]
          inext
          iapply (writer_read γ SW Rw σ HRw.1) $$ Hsw HSW
          iintro HSW %item %ok ⟨%Hitem, #Hold, Hr⟩
          obtain ⟨rfl, rfl⟩ := Hitem
          (try wp_auto)
          wp_apply (wp_mapInsert go.string m M (KF o) o) $$ [$Hm] as Hm
          (try wp_auto)
          have hcur0 : objAt ((ds.take (sint.nat n)).foldl (fdItems KF) σ.items) (KF o) =
              objAt σ.items (KF o) := by rw [HM, hMk]; rfl
          generalize objAt σ.items (KF o) = ov at hcur0 ⊢
          cases ov with
          | nil =>
            simp only
            (try wp_auto)
            ipersist obj
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l1 ⟨Hl1, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Htsl $Htcap $Hl1] as %tsl' ⟨Htsl, Htcap, -⟩
            (try wp_auto)
            wp_func_lits
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l2 ⟨Hl2, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hcsl $Hccap $Hl2] as %csl' ⟨Hcsl, Hccap, -⟩
            (try wp_auto)
            wp_for_post
            have htx : (batchTxs KF σ.items (ds.take (sint.nat n) ++ [FD.obj t o])).map Tx.txn =
                (batchTxs KF σ.items (ds.take (sint.nat n))).map Tx.txn ++
                  [Transaction.mk o go!"Add"] := by
              rw [batchTxs_snoc, List.map_append]; simp [fdTx, ht, hcur0, Tx.txn]
            have hev : batchEvs KF b σ.items (ds.take (sint.nat n) ++ [FD.obj t o]) =
                batchEvs KF b σ.items (ds.take (sint.nat n)) ++ [Ev.add o b] := by
              rw [batchEvs_snoc]; simp [fdEv, putEvR, ht, hcur0]
            iframe
            iexists n + W64 1, _, tsl', csl', _, <[KF o := o]> M
            rw [htake, htx, hev]
            iframe
            isplitr
            · imodintro
              iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ f e => cbOk H f e)).2
              isplitl
              · iexact Hcbs
              iunfold cbOk
              iintro %evs' %Φ' !> HH' HΦ'
              wp_pures
              (try wp_auto)
              ihave #HA := HonAdd $$ %evs' %o %b
              wp_bind (App (App (Val #(methods hi.ty go!"OnAdd" hi.v)) _) _)
              iapply HA $$ [$HH' $HOKo]
              inext
              iintro HH'
              (try wp_auto)
              iapply HΦ'; iexact HH'
            ipureintro
            refine ⟨inBatch_step KF σ.items _ M _ o o (by simp [ht]) HM,
              inBatch_vals KF _ M o o hoin (Or.inr rfl) HMv, by word⟩
          | ok oi =>
            simp only
            (try wp_auto)
            ipersist old
            ipersist obj
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l1 ⟨Hl1, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Htsl $Htcap $Hl1] as %tsl' ⟨Htsl, Htcap, -⟩
            (try wp_auto)
            wp_func_lits
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l2 ⟨Hl2, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hcsl $Hccap $Hl2] as %csl' ⟨Hcsl, Hccap, -⟩
            (try wp_auto)
            wp_for_post
            have htx : (batchTxs KF σ.items (ds.take (sint.nat n) ++ [FD.obj t o])).map Tx.txn =
                (batchTxs KF σ.items (ds.take (sint.nat n))).map Tx.txn ++
                  [Transaction.mk o go!"Update"] := by
              rw [batchTxs_snoc, List.map_append]; simp [fdTx, ht, hcur0, Tx.txn]
            have hev : batchEvs KF b σ.items (ds.take (sint.nat n) ++ [FD.obj t o]) =
                batchEvs KF b σ.items (ds.take (sint.nat n)) ++ [Ev.update (GoInterface.ok oi) o] := by
              rw [batchEvs_snoc]; simp [fdEv, putEvR, ht, hcur0]
            iframe
            iexists n + W64 1, _, tsl', csl', _, <[KF o := o]> M
            rw [htake, htx, hev]
            iframe
            isplitr
            · imodintro
              iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ f e => cbOk H f e)).2
              isplitl
              · iexact Hcbs
              iunfold cbOk
              iintro %evs' %Φ' !> HH' HΦ'
              wp_pures
              (try wp_auto)
              ihave #HU := HonUpd $$ %evs' %(GoInterface.ok oi) %o
              wp_bind (App (App (Val #(methods hi.ty go!"OnUpdate" hi.v)) _) _)
              iapply HU $$ [$HH' $Hold $HOKo]
              inext
              iintro HH'
              (try wp_auto)
              iapply HΦ'; iexact HH'
            ipureintro
            refine ⟨inBatch_step KF σ.items _ M _ o o (by simp [ht]) HM,
              inBatch_vals KF _ M o o hoin (Or.inr rfl) HMv, by word⟩
        · simp only [Option.isSome_some, Option.getD_some, _root_.decide_true, Bool.not_true]
          (try wp_auto)
          wp_apply (wp_mapInsert go.string m M (KF o) o) $$ [$Hm] as Hm
          (try wp_auto)
          ihave #Hold : okNil OK x $$ []
          · rcases HMv _ _ hMk with hx | hx
            · iunfold okNil; ileft; ipureintro; exact hx
            · obtain ⟨d', hd', hdx⟩ := List.mem_map.1 hx
              iunfold okNil; iright; imodintro
              rw [← hdx]
              ihave #Hx := BigSepL.bigSepL_mem (Φ := fun (d : FD) => iprop(OK d.obj?)) hd' $$ Hoks
              iexact Hx
          have hcur0 : objAt ((ds.take (sint.nat n)).foldl (fdItems KF) σ.items) (KF o) = x := by
            rw [HM, hMk]; rfl
          generalize x = ov at hcur0 ⊢
          cases ov with
          | nil =>
            simp only
            (try wp_auto)
            ipersist obj
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l1 ⟨Hl1, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Htsl $Htcap $Hl1] as %tsl' ⟨Htsl, Htcap, -⟩
            (try wp_auto)
            wp_func_lits
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l2 ⟨Hl2, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hcsl $Hccap $Hl2] as %csl' ⟨Hcsl, Hccap, -⟩
            (try wp_auto)
            wp_for_post
            have htx : (batchTxs KF σ.items (ds.take (sint.nat n) ++ [FD.obj t o])).map Tx.txn =
                (batchTxs KF σ.items (ds.take (sint.nat n))).map Tx.txn ++
                  [Transaction.mk o go!"Add"] := by
              rw [batchTxs_snoc, List.map_append]; simp [fdTx, ht, hcur0, Tx.txn]
            have hev : batchEvs KF b σ.items (ds.take (sint.nat n) ++ [FD.obj t o]) =
                batchEvs KF b σ.items (ds.take (sint.nat n)) ++ [Ev.add o b] := by
              rw [batchEvs_snoc]; simp [fdEv, putEvR, ht, hcur0]
            iframe
            iexists n + W64 1, _, tsl', csl', _, <[KF o := o]> M
            rw [htake, htx, hev]
            iframe
            isplitr
            · imodintro
              iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ f e => cbOk H f e)).2
              isplitl
              · iexact Hcbs
              iunfold cbOk
              iintro %evs' %Φ' !> HH' HΦ'
              wp_pures
              (try wp_auto)
              ihave #HA := HonAdd $$ %evs' %o %b
              wp_bind (App (App (Val #(methods hi.ty go!"OnAdd" hi.v)) _) _)
              iapply HA $$ [$HH' $HOKo]
              inext
              iintro HH'
              (try wp_auto)
              iapply HΦ'; iexact HH'
            ipureintro
            refine ⟨inBatch_step KF σ.items _ M _ o o (by simp [ht]) HM,
              inBatch_vals KF _ M o o hoin (Or.inr rfl) HMv, by word⟩
          | ok oi =>
            simp only
            (try wp_auto)
            ipersist old
            ipersist obj
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l1 ⟨Hl1, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Htsl $Htcap $Hl1] as %tsl' ⟨Htsl, Htcap, -⟩
            (try wp_auto)
            wp_func_lits
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l2 ⟨Hl2, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hcsl $Hccap $Hl2] as %csl' ⟨Hcsl, Hccap, -⟩
            (try wp_auto)
            wp_for_post
            have htx : (batchTxs KF σ.items (ds.take (sint.nat n) ++ [FD.obj t o])).map Tx.txn =
                (batchTxs KF σ.items (ds.take (sint.nat n))).map Tx.txn ++
                  [Transaction.mk o go!"Update"] := by
              rw [batchTxs_snoc, List.map_append]; simp [fdTx, ht, hcur0, Tx.txn]
            have hev : batchEvs KF b σ.items (ds.take (sint.nat n) ++ [FD.obj t o]) =
                batchEvs KF b σ.items (ds.take (sint.nat n)) ++ [Ev.update (GoInterface.ok oi) o] := by
              rw [batchEvs_snoc]; simp [fdEv, putEvR, ht, hcur0]
            iframe
            iexists n + W64 1, _, tsl', csl', _, <[KF o := o]> M
            rw [htake, htx, hev]
            iframe
            isplitr
            · imodintro
              iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ f e => cbOk H f e)).2
              isplitl
              · iexact Hcbs
              iunfold cbOk
              iintro %evs' %Φ' !> HH' HΦ'
              wp_pures
              (try wp_auto)
              ihave #HU := HonUpd $$ %evs' %(GoInterface.ok oi) %o
              wp_bind (App (App (Val #(methods hi.ty go!"OnUpdate" hi.v)) _) _)
              iapply HU $$ [$HH' $Hold $HOKo]
              inext
              iintro HH'
              (try wp_auto)
              iapply HΦ'; iexact HH'
            ipureintro
            refine ⟨inBatch_step KF σ.items _ M _ o o (by simp [ht]) HM,
              inBatch_vals KF _ M o o hoin (Or.inr rfl) HMv, by word⟩
      · rw [ht']
        rw [decide_eq_true rfl]
        (try wp_auto)
        rw [← ht']
        wp_apply (wp_map_lookup2 go.string (go.GoType.InterfaceType []) m M (KF o) (DFrac.own 1))
          $$ [$Hm] as Hm
        rcases hMk : M !! KF o with _ | x
        · simp only [Option.isSome_none, Option.getD_none]
          (try wp_auto)
          wp_bind
          iapply (wp_GetByKey ca ts γ OK Fam kf (KF o)) $$ [$Hpkg $Hca $Hr]
          inext
          iapply (writer_read γ SW Rw σ HRw.1) $$ Hsw HSW
          iintro HSW %item %ok ⟨%Hitem, #Hold, Hr⟩
          obtain ⟨rfl, rfl⟩ := Hitem
          (try wp_auto)
          wp_apply (wp_mapInsert go.string m M (KF o) o) $$ [$Hm] as Hm
          (try wp_auto)
          have hcur0 : objAt ((ds.take (sint.nat n)).foldl (fdItems KF) σ.items) (KF o) =
              objAt σ.items (KF o) := by rw [HM, hMk]; rfl
          generalize objAt σ.items (KF o) = ov at hcur0 ⊢
          cases ov with
          | nil =>
            simp only
            (try wp_auto)
            ipersist obj
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l1 ⟨Hl1, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Htsl $Htcap $Hl1] as %tsl' ⟨Htsl, Htcap, -⟩
            (try wp_auto)
            wp_func_lits
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l2 ⟨Hl2, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hcsl $Hccap $Hl2] as %csl' ⟨Hcsl, Hccap, -⟩
            (try wp_auto)
            wp_for_post
            have htx : (batchTxs KF σ.items (ds.take (sint.nat n) ++ [FD.obj t o])).map Tx.txn =
                (batchTxs KF σ.items (ds.take (sint.nat n))).map Tx.txn ++
                  [Transaction.mk o go!"Add"] := by
              rw [batchTxs_snoc, List.map_append]; simp [fdTx, ht, hcur0, Tx.txn]
            have hev : batchEvs KF b σ.items (ds.take (sint.nat n) ++ [FD.obj t o]) =
                batchEvs KF b σ.items (ds.take (sint.nat n)) ++ [Ev.add o b] := by
              rw [batchEvs_snoc]; simp [fdEv, putEvR, ht, hcur0]
            iframe
            iexists n + W64 1, _, tsl', csl', _, <[KF o := o]> M
            rw [htake, htx, hev]
            iframe
            isplitr
            · imodintro
              iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ f e => cbOk H f e)).2
              isplitl
              · iexact Hcbs
              iunfold cbOk
              iintro %evs' %Φ' !> HH' HΦ'
              wp_pures
              (try wp_auto)
              ihave #HA := HonAdd $$ %evs' %o %b
              wp_bind (App (App (Val #(methods hi.ty go!"OnAdd" hi.v)) _) _)
              iapply HA $$ [$HH' $HOKo]
              inext
              iintro HH'
              (try wp_auto)
              iapply HΦ'; iexact HH'
            ipureintro
            refine ⟨inBatch_step KF σ.items _ M _ o o (by simp [ht]) HM,
              inBatch_vals KF _ M o o hoin (Or.inr rfl) HMv, by word⟩
          | ok oi =>
            simp only
            (try wp_auto)
            ipersist old
            ipersist obj
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l1 ⟨Hl1, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Htsl $Htcap $Hl1] as %tsl' ⟨Htsl, Htcap, -⟩
            (try wp_auto)
            wp_func_lits
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l2 ⟨Hl2, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hcsl $Hccap $Hl2] as %csl' ⟨Hcsl, Hccap, -⟩
            (try wp_auto)
            wp_for_post
            have htx : (batchTxs KF σ.items (ds.take (sint.nat n) ++ [FD.obj t o])).map Tx.txn =
                (batchTxs KF σ.items (ds.take (sint.nat n))).map Tx.txn ++
                  [Transaction.mk o go!"Update"] := by
              rw [batchTxs_snoc, List.map_append]; simp [fdTx, ht, hcur0, Tx.txn]
            have hev : batchEvs KF b σ.items (ds.take (sint.nat n) ++ [FD.obj t o]) =
                batchEvs KF b σ.items (ds.take (sint.nat n)) ++ [Ev.update (GoInterface.ok oi) o] := by
              rw [batchEvs_snoc]; simp [fdEv, putEvR, ht, hcur0]
            iframe
            iexists n + W64 1, _, tsl', csl', _, <[KF o := o]> M
            rw [htake, htx, hev]
            iframe
            isplitr
            · imodintro
              iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ f e => cbOk H f e)).2
              isplitl
              · iexact Hcbs
              iunfold cbOk
              iintro %evs' %Φ' !> HH' HΦ'
              wp_pures
              (try wp_auto)
              ihave #HU := HonUpd $$ %evs' %(GoInterface.ok oi) %o
              wp_bind (App (App (Val #(methods hi.ty go!"OnUpdate" hi.v)) _) _)
              iapply HU $$ [$HH' $Hold $HOKo]
              inext
              iintro HH'
              (try wp_auto)
              iapply HΦ'; iexact HH'
            ipureintro
            refine ⟨inBatch_step KF σ.items _ M _ o o (by simp [ht]) HM,
              inBatch_vals KF _ M o o hoin (Or.inr rfl) HMv, by word⟩
        · simp only [Option.isSome_some, Option.getD_some, _root_.decide_true, Bool.not_true]
          (try wp_auto)
          wp_apply (wp_mapInsert go.string m M (KF o) o) $$ [$Hm] as Hm
          (try wp_auto)
          ihave #Hold : okNil OK x $$ []
          · rcases HMv _ _ hMk with hx | hx
            · iunfold okNil; ileft; ipureintro; exact hx
            · obtain ⟨d', hd', hdx⟩ := List.mem_map.1 hx
              iunfold okNil; iright; imodintro
              rw [← hdx]
              ihave #Hx := BigSepL.bigSepL_mem (Φ := fun (d : FD) => iprop(OK d.obj?)) hd' $$ Hoks
              iexact Hx
          have hcur0 : objAt ((ds.take (sint.nat n)).foldl (fdItems KF) σ.items) (KF o) = x := by
            rw [HM, hMk]; rfl
          generalize x = ov at hcur0 ⊢
          cases ov with
          | nil =>
            simp only
            (try wp_auto)
            ipersist obj
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l1 ⟨Hl1, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Htsl $Htcap $Hl1] as %tsl' ⟨Htsl, Htcap, -⟩
            (try wp_auto)
            wp_func_lits
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l2 ⟨Hl2, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hcsl $Hccap $Hl2] as %csl' ⟨Hcsl, Hccap, -⟩
            (try wp_auto)
            wp_for_post
            have htx : (batchTxs KF σ.items (ds.take (sint.nat n) ++ [FD.obj t o])).map Tx.txn =
                (batchTxs KF σ.items (ds.take (sint.nat n))).map Tx.txn ++
                  [Transaction.mk o go!"Add"] := by
              rw [batchTxs_snoc, List.map_append]; simp [fdTx, ht, hcur0, Tx.txn]
            have hev : batchEvs KF b σ.items (ds.take (sint.nat n) ++ [FD.obj t o]) =
                batchEvs KF b σ.items (ds.take (sint.nat n)) ++ [Ev.add o b] := by
              rw [batchEvs_snoc]; simp [fdEv, putEvR, ht, hcur0]
            iframe
            iexists n + W64 1, _, tsl', csl', _, <[KF o := o]> M
            rw [htake, htx, hev]
            iframe
            isplitr
            · imodintro
              iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ f e => cbOk H f e)).2
              isplitl
              · iexact Hcbs
              iunfold cbOk
              iintro %evs' %Φ' !> HH' HΦ'
              wp_pures
              (try wp_auto)
              ihave #HA := HonAdd $$ %evs' %o %b
              wp_bind (App (App (Val #(methods hi.ty go!"OnAdd" hi.v)) _) _)
              iapply HA $$ [$HH' $HOKo]
              inext
              iintro HH'
              (try wp_auto)
              iapply HΦ'; iexact HH'
            ipureintro
            refine ⟨inBatch_step KF σ.items _ M _ o o (by simp [ht]) HM,
              inBatch_vals KF _ M o o hoin (Or.inr rfl) HMv, by word⟩
          | ok oi =>
            simp only
            (try wp_auto)
            ipersist old
            ipersist obj
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l1 ⟨Hl1, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Htsl $Htcap $Hl1] as %tsl' ⟨Htsl, Htcap, -⟩
            (try wp_auto)
            wp_func_lits
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l2 ⟨Hl2, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hcsl $Hccap $Hl2] as %csl' ⟨Hcsl, Hccap, -⟩
            (try wp_auto)
            wp_for_post
            have htx : (batchTxs KF σ.items (ds.take (sint.nat n) ++ [FD.obj t o])).map Tx.txn =
                (batchTxs KF σ.items (ds.take (sint.nat n))).map Tx.txn ++
                  [Transaction.mk o go!"Update"] := by
              rw [batchTxs_snoc, List.map_append]; simp [fdTx, ht, hcur0, Tx.txn]
            have hev : batchEvs KF b σ.items (ds.take (sint.nat n) ++ [FD.obj t o]) =
                batchEvs KF b σ.items (ds.take (sint.nat n)) ++ [Ev.update (GoInterface.ok oi) o] := by
              rw [batchEvs_snoc]; simp [fdEv, putEvR, ht, hcur0]
            iframe
            iexists n + W64 1, _, tsl', csl', _, <[KF o := o]> M
            rw [htake, htx, hev]
            iframe
            isplitr
            · imodintro
              iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ f e => cbOk H f e)).2
              isplitl
              · iexact Hcbs
              iunfold cbOk
              iintro %evs' %Φ' !> HH' HΦ'
              wp_pures
              (try wp_auto)
              ihave #HU := HonUpd $$ %evs' %(GoInterface.ok oi) %o
              wp_bind (App (App (Val #(methods hi.ty go!"OnUpdate" hi.v)) _) _)
              iapply HU $$ [$HH' $Hold $HOKo]
              inext
              iintro HH'
              (try wp_auto)
              iapply HΦ'; iexact HH'
            ipureintro
            refine ⟨inBatch_step KF σ.items _ M _ o o (by simp [ht]) HM,
              inBatch_vals KF _ M o o hoin (Or.inr rfl) HMv, by word⟩
      · exact absurd ht' ht
  · have hn : sint.nat n = ds.length := by
      have := Hlen.1; simp only [List.length_map] at this; word
    rw [hn, List.take_length] at *
    (try wp_auto)
    have hkeyed : (batchTxs KF σ.items ds).map (Tx.keyed KF) = batchTxs KF σ.items ds := by
      have hx : ∀ x ∈ batchTxs KF σ.items ds, Tx.keyed KF x = x := fun x hx => by
        have := batchTxs_keyed KF ds σ.items x hx
        cases x; simp only [Tx.keyed] at this ⊢; rw [this]
      exact (List.map_congr_left hx).trans (List.map_id _)
    wp_bind
    iapply (wp_Txn ca ts γ OK Fam kf (fun x => iprop(⌜x ∈ ds.map FD.obj?⌝)) KF rvOf tsl (DFrac.own 1)
      (batchTxs KF σ.items ds) hty) $$ [$Hpkg $Hca $Hkey $Hacc $Htsl]
    · isplitr
      · ipureintro; exact batchTxs_typeOk KF ds σ.items
      imodintro
      iapply (BigSepL.bigSepL_intro (P := iprop(□ [∗list] d ∈ ds, OK d.obj?))
        (Φ := fun _ (x : Tx) => iprop(⌜x.o ∈ ds.map FD.obj?⌝ ∗ OK x.o)) ?_) $$ Hoks
      intro k x hx
      have hxo := batchTxs_objs KF ds σ.items x (List.mem_of_getElem? hx)
      obtain ⟨d', hd', hdx⟩ := List.mem_map.1 hxo
      iintro #H
      isplitr
      · ipureintro; exact hxo
      rw [← hdx]
      iapply (BigSepL.bigSepL_mem (Φ := fun (d : FD) => iprop(OK d.obj?)) hd') $$ H
    inext
    iapply (writer_step γ SW Rw σ (fun σ' => St.txn rvOf σ' ((batchTxs KF σ.items ds).map (Tx.keyed KF)))
      (by rw [hkeyed, txn_batchTxs KF rvOf σ ds Hobj']; exact HRw.2))
      $$ Hsw HSW
    iintro HSW Htsl
    rw [hkeyed, txn_batchTxs KF rvOf σ ds Hobj']
    (try wp_auto)
    ihave %Hfl := BigSepL2.bigSepL2_length $$ Hcbs
    ihave %Hcl := ownSlice_len _ _ _ $$ Hcsl
    ihave IH2 : iprop(∃ (j : w64) (cv : GoFunc),
        "i" ∷ i_ptr ↦ j ∗ "callback" ∷ callback_ptr ↦ cv ∗
        "HH" ∷ H (evs ++ (batchEvs KF b σ.items ds).take (sint.nat j)) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z csl.len⌝) $$ [i callback HH]
    · iexists W64 0, _
      iframe
      rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.append_nil]
      iframe
      ipureintro; word
    wp_for IH2
    wp_if_destruct
    · have Hlt : sint.nat j < fs.length := by word
      obtain ⟨f, Hf⟩ : ∃ f, fs[sint.nat j]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨e, He⟩ : ∃ e, (batchEvs KF b σ.items ds)[sint.nat j]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hfl]; exact Hlt)⟩
      ihave #Hcb := BigSepL2.bigSepL2_lookup (Φ := fun _ f e => cbOk H f e) Hf He $$ Hcbs
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z csl.len from ⟨Hj.1, Hif⟩, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index csl (sint.Z j) fs (DFrac.own 1) f Hj.1 $$ [Hcsl] as Hcsl
      · iframe; ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact Hf
      (try wp_auto)
      iunfold cbOk at Hcb
      ihave #Hcb1 := Hcb $$ %(evs ++ (batchEvs KF b σ.items ds).take (sint.nat j))
      wp_bind (App (Val #f) (Val #()))
      iapply Hcb1 $$ [$HH]
      inext
      iintro HH
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _
      iframe
      have : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [this, List.take_add_one, He]
      simp only [Option.toList_some, List.append_assoc]
      iframe
      ipureintro; word
    · have hj : sint.nat j = (batchEvs KF b σ.items ds).length := by
        rw [← Hfl]; have := Hcl.1; word
      rw [hj, List.take_length]
      (try wp_auto)
      ihave Hnil := ownSlice_nil (GF := GF) (V := GoInterface) (DFrac.own 1)
      wp_apply (wp_Join slice.nil (DFrac.own 1) []) $$ [$Hnil] as %e ⟨%He, -⟩
      rw [He (by simp)]
      (try wp_auto)
      iapply HΦ
      iexists _, _
      iframe
      ipureintro
      exact ⟨rfl, rfl⟩

end proof

end cache
end EtcdGrove
end Perennial
