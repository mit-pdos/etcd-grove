module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Common
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Store
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Log
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.CommitM
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.UpdSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

section reqprop
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

instance itemPtr_persistent_rp (p : Loc) (k : GoString) (v : w64) (x : GoString) :
    Persistent (itemPtr (hG := hG) p k v x) := by
  unfold itemPtr; infer_instance

instance respItems_persistent (γ : CraqNames) (resp : GMap GoString (List (GoString × w64))) :
    Persistent (respItems (GF := GF) γ resp) := by
  unfold respItems; infer_instance

instance respCommitted_persistent (γ : CraqNames) (resp : GMap GoString (List (GoString × w64))) :
    Persistent (respCommitted (GF := GF) γ resp) := by
  unfold respCommitted; infer_instance

/-- `propagateRequestFromItems(items)`: each key's request version is some item's. -/
theorem wp_propagateRequestFromItems (sl : GoSlice) (ps : List Loc)
    (es : List (GoString × w64 × GoString × Bool)) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ sl ↦* ps ∗
        [∗list] i ↦ p ∈ ps, ∃ e, ⌜es[i]? = some e⌝ ∗ itemPtr p e.1 e.2.1 e.2.2.1) -∗
      (∀ (ptr : Loc) (req : GMap GoString w64), reqPtr ptr (DFrac.own 1) req -∗ sl ↦* ps -∗
        ⌜∀ k, reqVer req k = W64 0 ∨ ∃ e ∈ es, e.1 = k ∧ e.2.1 = reqVer req k⌝ -∗
        ⌜∀ k v, req.lookup k = some v → ∃ e ∈ es, e.1 = k⌝ -∗ Φ #ptr) -∗
      WP (App (Val (@! node.propagateRequestFromItems)) (Val #sl)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, Hsl, #Hps⟩ HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w64)) as %mp Hmp
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (j : w64) (it : Loc) (m : GMap GoString w64),
      "i" ∷ i_ptr ↦ j ∗ "item" ∷ item_ptr ↦ it ∗ "Hmp" ∷ mp ↦$ m ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (ps.length : Int)⌝ ∗
      "%Hm" ∷ ⌜∀ k, reqVer m k = W64 0 ∨ ∃ e ∈ es, e.1 = k ∧ e.2.1 = reqVer m k⌝ ∗
      "%Hd" ∷ ⌜∀ k v, m.lookup k = some v → ∃ e ∈ es, e.1 = k⌝) $$ [i item Hmp]
  · iexists _, _, ∅
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, fun k => Or.inl ?_, fun k v h => ?_⟩
    · simp [reqVer]
    · simp at h
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z j).toNat < ps.length := by word
    obtain ⟨p, Hp⟩ : ∃ p, ps[(sint.Z j).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z j) ps (DFrac.own 1) p Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hp
    ihave #Hp := BI.BigSepL.bigSepL_lookup
      (Φ := fun i p => iprop(∃ e, ⌜es[i]? = some e⌝ ∗ itemPtr (hG := hG) p e.1 e.2.1 e.2.2.1)) Hp $$ Hps
    icases Hp with ⟨%e, %He, #Hip⟩
    unfold itemPtr
    icases Hip with ⟨#Hk, #Hv, -⟩
    wp_auto
    wp_apply wp_map_lookup1 $$ Hmp with Hmp
    have hemem : e ∈ es := List.mem_of_getElem? He
    wp_if_destruct
    · wp_apply wp_mapInsert $$ Hmp with Hmp
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, fun k => ?_, fun k v h => ?_⟩
      · by_cases hk : k = e.1
        · subst hk
          right; refine ⟨e, hemem, rfl, ?_⟩
          simp [reqVer, GMap.lookup_insert_eq]
        · have : reqVer (<[e.1 := e.2.1]> m) k = reqVer m k := by
            simp only [reqVer]; rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]
          rw [this]; exact Hm k
      · by_cases hk : k = e.1
        · subst hk; exact ⟨e, hemem, rfl⟩
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at h
          exact Hd k v h
    · wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      exact ⟨⟨by word, by word⟩, Hm, Hd⟩
  · iapply HΦ $$ [req Hmp] Hsl
    · unfold reqPtr; iexists mp; iframe
    · ipureintro; exact Hm
    ipureintro; exact Hd

/-- A request built from a store's items has keys the protocol handles. -/
theorem reqKeysOk_of (S : StoreS) (es : List (GoString × w64 × GoString × Bool))
    (req : GMap GoString w64) (HSk : ∀ e ∈ S, keyOk e.1)
    (Hes : ∀ e ∈ es, (e.2.1, e.2.2.1, e.2.2.2) ∈ S.items e.1)
    (Hd : ∀ k v, req.lookup k = some v → ∃ e ∈ es, e.1 = k) : reqKeysOk req := by
  intro k v h
  obtain ⟨e, he, rfl⟩ := Hd k v h
  obtain ⟨e', he', hk⟩ := StoreS.mem_items_key S e.1 _ (Hes e he)
  exact hk ▸ HSk e' he'

/-- The reply's slices (`respPtr`'s big separating conjunction). -/
def respSlices (m : GMap GoString GoSlice) (resp : GMap GoString (List (GoString × w64))) : IProp GF :=
  iprop([∗map] k ↦ sl ∈ m, ∃ (vvs : List transport.ValueVersion),
      sl ↦* vvs ∗ ⌜vvs.map (·.Version') = ((resp.lookup k).getD []).map Prod.snd⌝ ∗
      [∗list] i ↦ vv ∈ vvs, ∃ x, ⌜(((resp.lookup k).getD [])[i]?).map Prod.fst = some x⌝ ∗
        vv.Value' ↦*□ x)

/-- The lock's store half, to be given back at contents with the same newest committed
versions. -/
theorem lockedState_store (cfg : Cfg GF) (γs : GName) (n nbM latM : Loc) (h t : Bool)
    (nbrs : GMap w64 node.neighbor) (lat : GMap GoString w64) (S : StoreS) :
    lockedState cfg γs n nbM latM h t nbrs lat S ⊢
      storeOwn γs (1 : Qp).half S ∗ (∀ S' : StoreS, storeOwn γs (1 : Qp).half S' -∗
        ⌜∀ k, S'.maxCommitted k = S.maxCommitted k⌝ -∗ lockedState cfg γs n nbM latM h t nbrs lat S') := by
  unfold lockedState
  iintro ⟨Hh, Ht, Hnbm, Hlatm, #Hnbrs, HS, %HlatS, Htail⟩
  iframe HS
  iintro %S' HS' %Hmc
  iframe; iframe #
  ipureintro
  intro k; rw [Hmc k]; exact HlatS k

theorem hasVer_write_rp (S : StoreS) (k x : GoString) (v : w64) : (S.write k x v).hasVer k v = true :=
  (StoreS.hasVer_iff _ k v).2 ⟨x, false, (StoreS.mem_write S k x v _).2 (Or.inr rfl)⟩

theorem mc_commit_ge (S : StoreS) (k : GoString) (v : w64) (hv : S.hasVer k v = true) :
    (∀ k', uint.Z (S.maxCommitted k') ≤ uint.Z ((S.commit k v).maxCommitted k')) ∧
    uint.Z v ≤ uint.Z ((S.commit k v).maxCommitted k) := by
  constructor
  · intro k'
    rw [StoreS.maxCommitted_commit S k v hv]
    split
    · rename_i h
      rcases h with ⟨rfl, h⟩; omega
    · omega
  · rw [StoreS.maxCommitted_commit S k v hv]
    split
    · omega
    · rename_i h; simp only [true_and] at h; omega

/-- The store package's error variables. -/
theorem store_vars :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store ⊢
      errors.newVar store.ErrNotFound go!"that key does not exist" ∗
      errors.newVar store.ErrDirtyItem go!"key has an uncommitted version" := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store

/-- `store.ErrNotFound`'s value is a pointer error. -/
theorem errNotFound_ptr (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store ∗ errNotFound err ⊢
      ⌜∃ x : Loc, err = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x⌝ := by
  iintro ⟨-, #Herr⟩
  unfold errNotFound
  icases Herr with ⟨%x, %h, -⟩
  ipureintro; exact ⟨x, h⟩

/-- The response list's entry at `j`, from the reply's slice of the key. -/
theorem resp_entry (resp : GMap GoString (List (GoString × w64))) (key : GoString)
    (vvs : List transport.ValueVersion) (j : Nat) (vv : transport.ValueVersion)
    (hv : vvs[j]? = some vv)
    (hver : vvs.map (fun x => x.Version') = ((resp !! key).getD []).map Prod.snd) :
    ([∗list] i ↦ vv ∈ vvs, ∃ x : GoString, ⌜(((resp !! key).getD [])[i]?).map Prod.fst = some x⌝ ∗
        (vv.Value' ↦*□ x : IProp GF)) ⊢
      ∃ x : GoString, vv.Value' ↦*□ x ∗
        ⌜((resp !! key).getD [])[j]? = some (x, vv.Version')⌝ := by
  iintro Hl
  ihave ⟨%x, %hx, #Hx⟩ := BI.BigSepL.bigSepL_lookup
    (Φ := fun i (vv : transport.ValueVersion) => iprop(∃ x : GoString,
        ⌜(((resp !! key).getD [])[i]?).map Prod.fst = some x⌝ ∗ (vv.Value' ↦*□ x : IProp GF))) hv $$ Hl
  iexists x
  iframe Hx
  ipureintro
  have h1 : (vvs.map (fun x => x.Version'))[j]? = some vv.Version' := by simp [hv]
  rw [hver, List.getElem?_map] at h1
  cases hl : ((resp !! key).getD [])[j]? with
  | none => simp [hl] at h1
  | some e =>
    rw [hl] at h1 hx
    simp only [Option.map_some, Option.some.injEq] at h1 hx
    rw [← h1, ← hx]

theorem resp_items_at (γ : CraqNames) (resp : GMap GoString (List (GoString × w64)))
    (key : GoString) (j : Nat) (x : GoString) (v : w64)
    (hj : ((resp !! key).getD [])[j]? = some (x, v)) :
    respItems (GF := GF) γ resp ⊢ valsElem γ v key x := by
  unfold respItems
  cases hk : resp !! key with
  | none => rw [hk] at hj; simp at hj
  | some l =>
    rw [hk] at hj
    simp only [Option.getD_some] at hj
    iintro Hm
    ihave Hl := BI.BigSepM.bigSepM_lookup
      (Φ := fun k (vvs : List (GoString × w64)) => iprop([∗list] e ∈ vvs, valsElem (GF := GF) γ e.2 k e.1)) hk $$ Hm
    iapply BI.BigSepL.bigSepL_lookup (Φ := fun _ (e : GoString × w64) => valsElem (GF := GF) γ e.2 key e.1) hj $$ Hl

theorem resp_committed_at (γ : CraqNames) (resp : GMap GoString (List (GoString × w64)))
    (key : GoString) (j : Nat) (x : GoString) (v : w64)
    (hj : ((resp !! key).getD [])[j]? = some (x, v)) :
    respCommitted (GF := GF) γ resp ⊢ cvLb γ key v := by
  unfold respCommitted
  cases hk : resp !! key with
  | none => rw [hk] at hj; simp at hj
  | some l =>
    rw [hk] at hj
    simp only [Option.getD_some] at hj
    iintro Hm
    ihave Hl := BI.BigSepM.bigSepM_lookup
      (Φ := fun k (vvs : List (GoString × w64)) => iprop([∗list] e ∈ vvs, cvLb (GF := GF) γ k e.2)) hk $$ Hm
    iapply BI.BigSepL.bigSepL_lookup (Φ := fun _ (e : GoString × w64) => cvLb (GF := GF) γ key e.2) hj $$ Hl

/-- `n.writePropagated(reply)` under the lock: every item of the reply written. -/
theorem wp_writePropagated (cfg : Cfg GF) (n : Loc) (a : GoString) (st : GoInterface)
    (γs : GName) (nbM latM : Loc) (h t : Bool) (nbrs : GMap w64 node.neighbor)
    (lat : GMap GoString w64) (S : StoreS) (rp : Loc)
    (resp : GMap GoString (List (GoString × w64))) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ craqCtx cfg ∗
        nodeFields cfg n a st γs nbM latM ∗ lockedState cfg γs n nbM latM h t nbrs lat S ∗
        respPtr rp resp ∗ respItems cfg.γ resp) -∗
      (∀ err : GoInterface, (∃ S' : StoreS, lockedState cfg γs n nbM latM h t nbrs lat S') -∗
        (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"writePropagated" #n))
        (Val #rp)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hctx, #Hf, Hls, Hresp, #Hitems⟩ HΦ
  ihave #Hf' := Hf
  iunfold nodeFields at Hf'
  icases Hf' with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  ihave #Hstore' := Hstore
  iunfold isStore at Hstore'
  icases Hstore' with ⟨%e, %he, -⟩
  subst he
  unfold respPtr
  icases Hresp with ⟨%mp, %m, Hrp, Hmp, %Hdom, Hsls⟩
  wp_method_call
  wp_call
  wp_auto
  ihave Hsls : respSlices m resp $$ [Hsls]
  · unfold respSlices; iexact Hsls
  wp_apply (wp_map_for_range (K := GoString) (V := GoSlice)
    (fun _ _ => iprop(∃ (S' : StoreS) (fk : GoSlice) (ky : GoString),
      lockedState cfg γs n nbM latM h t nbrs lat S' ∗ forKey_ptr ↦ fk ∗ key_ptr ↦ ky ∗
      n_ptr ↦ n ∗ respSlices m resp))) $$ Hmp
  iintro %keys %Hkeys
  isplitl [Hls forKey key Hsls n]
  · iexists S, _, _; iframe
  isplitr
  · imodintro
    iintro %i %key %sl %Hkv ⟨%S', %fk, %ky, Hls, forKey, key, Hn, Hsls⟩
    wp_auto
    unfold respSlices
    ihave ⟨⟨%vvs, Hvvs, %Hver, #Hvals⟩, Hclose⟩ := (BI.BigSepM.bigSepM_lookup_acc
      (Φ := fun k (sl : GoSlice) => iprop(∃ (vvs : List transport.ValueVersion),
      sl ↦* vvs ∗ ⌜vvs.map (·.Version') = ((resp.lookup k).getD []).map Prod.snd⌝ ∗
      [∗list] i ↦ vv ∈ vvs, ∃ x, ⌜(((resp.lookup k).getD [])[i]?).map Prod.fst = some x⌝ ∗
        vv.Value' ↦*□ x)) Hkv.2).1 $$ Hsls
    ihave %Hlen := ownSlice_len $$ Hvvs
    ihave IH : iprop(∃ (j : w64) (itv : transport.ValueVersion) (S'' : StoreS),
        "i" ∷ i_ptr ↦ j ∗ "item" ∷ item_ptr ↦ itv ∗
        "Hls" ∷ lockedState cfg γs n nbM latM h t nbrs lat S'' ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (vvs.length : Int)⌝) $$ [i item Hls]
    · iexists _, _, _
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    wp_for IH
    wp_if_destruct
    · have Hlt : (sint.Z j).toNat < vvs.length := by word
      obtain ⟨vv, Hvv⟩ : ∃ vv, vvs[(sint.Z j).toNat]? = some vv :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj.1, Hif⟩]
      wp_apply wp_load_slice_index sl (sint.Z j) vvs (DFrac.own 1) vv Hj.1 $$ [Hvvs] as Hvvs
      · iframe; ipureintro; exact Hvv
      ihave ⟨%x, #Hx, %Hx⟩ := resp_entry resp key vvs _ vv Hvv Hver $$ Hvals
      ihave #Hve := resp_items_at cfg.γ resp key _ x vv.Version' Hx $$ Hitems
      ihave ⟨HS, Hback⟩ := lockedState_store cfg γs n nbM latM h t nbrs lat S'' $$ Hls
      wp_apply (wp_store_Write cfg a γs e S'' key vv.Value' x vv.Version') $$ [$Hstore $Hinv $HS $Hx $Hve]
      iintro HS
      ihave Hls := Hback $$ %(S''.write key x vv.Version') HS %(StoreS.maxCommitted_write S'' key x vv.Version')
      wp_auto
      wp_log [interface.mkOk go.string #key]
      · iapply argOks1; iapply argOk_string
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    · ihave Hsls := Hclose $$ [Hvvs]
      · iexists vvs; iframe; iframe #; ipureintro; exact Hver
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _, _
      iframe
  · iintro ⟨%S', %fk, %ky, Hls, forKey, key, Hn, Hsls⟩ Hmp
    wp_auto
    iapply HΦ $$ [Hls]
    · iexists S'; iexact Hls
    ileft; ipureintro; rfl

/-- Every item of the reply, as far as processed, is at most the store's newest committed version
of its key. -/
def respBelow (resp : GMap GoString (List (GoString × w64))) (S : StoreS) (k : GoString)
    (n : Nat) : Prop :=
  ∀ (j : Nat) (x : GoString) (v : w64), j < n → ((resp !! k).getD [])[j]? = some (x, v) → uint.Z v ≤ uint.Z (S.maxCommitted k)

theorem respBelow_mono (resp : GMap GoString (List (GoString × w64))) (S S' : StoreS)
    (k : GoString) (n : Nat) (hm : ∀ k, uint.Z (S.maxCommitted k) ≤ uint.Z (S'.maxCommitted k))
    (h : respBelow resp S k n) : respBelow resp S' k n :=
  fun j x v hj hl => Int.le_trans (h j x v hj hl) (hm k)

/-- `n.commitPropagated(reply)` under the lock: every item of the reply committed. -/
theorem wp_commitPropagated (HL : Laws (GF := GF)) (cfg : Cfg GF) (n : Loc) (a : GoString)
    (st : GoInterface) (γs : GName) (nbM latM : Loc) (h t : Bool) (nbrs : GMap w64 node.neighbor)
    (lat : GMap GoString w64) (S : StoreS) (rp : Loc)
    (resp : GMap GoString (List (GoString × w64))) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ craqCtx cfg ∗
        nodeFields cfg n a st γs nbM latM ∗ lockedState cfg γs n nbM latM h t nbrs lat S ∗
        respPtr rp resp ∗ respItems cfg.γ resp ∗ respCommitted cfg.γ resp) -∗
      (∀ err : GoInterface, (∃ (lat' : GMap GoString w64) (S' : StoreS),
          lockedState cfg γs n nbM latM h t nbrs lat' S' ∗
          ⌜∀ k, uint.Z (S.maxCommitted k) ≤ uint.Z (S'.maxCommitted k)⌝ ∗
          ⌜err = interface.nil → ∀ (k : GoString) (j : Nat) (x : GoString) (v : w64),
            ((resp !! k).getD [])[j]? = some (x, v) →
            uint.Z v ≤ uint.Z (S'.maxCommitted k)⌝) -∗
        (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"commitPropagated" #n))
        (Val #rp)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hctx, #Hf, Hls, Hresp, #Hitems, #Hcomm⟩ HΦ
  ihave #Hf' := Hf
  iunfold nodeFields at Hf'
  icases Hf' with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  ihave #Hstore' := Hstore
  iunfold isStore at Hstore'
  icases Hstore' with ⟨%e, %he, -⟩
  subst he
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store $$ []
  · iPkgInit
  unfold respPtr
  icases Hresp with ⟨%mp, %m, Hrp, Hmp, %Hdom, Hsls⟩
  wp_method_call
  wp_call
  wp_auto
  ihave Hsls : respSlices m resp $$ [Hsls]
  · unfold respSlices; iexact Hsls
  wp_apply (wp_map_for_range (K := GoString) (V := GoSlice)
    (fun keys i => iprop(∃ (lat' : GMap GoString w64) (S' : StoreS) (fk : GoSlice) (ky : GoString),
      lockedState cfg γs n nbM latM h t nbrs lat' S' ∗ forKey_ptr ↦ fk ∗ key_ptr ↦ ky ∗
      n_ptr ↦ n ∗ respSlices m resp ∗
      ⌜∀ k, uint.Z (S.maxCommitted k) ≤ uint.Z (S'.maxCommitted k)⌝ ∗
      ⌜∀ (j : Nat) k, j < i.toNat → keys[j]? = some k → respBelow resp S' k
        ((resp !! k).getD []).length⌝))) $$ Hmp
  iintro %keys %Hkeys
  isplitl [Hls forKey key Hsls n]
  · iexists lat, S, _, _; iframe
    ipureintro
    exact ⟨fun k => Int.le_refl _, fun j k hj => by simp at hj⟩
  isplitr
  · imodintro
    iintro %i %key %sl %Hkv ⟨%lat', %S', %fk, %ky, Hls, forKey, key, Hn, Hsls, %Hmono, %Hdone⟩
    wp_auto
    unfold respSlices
    ihave ⟨⟨%vvs, Hvvs, %Hver, #Hvals⟩, Hclose⟩ := (BI.BigSepM.bigSepM_lookup_acc
      (Φ := fun k (sl : GoSlice) => iprop(∃ (vvs : List transport.ValueVersion),
      sl ↦* vvs ∗ ⌜vvs.map (·.Version') = ((resp.lookup k).getD []).map Prod.snd⌝ ∗
      [∗list] i ↦ vv ∈ vvs, ∃ x, ⌜(((resp.lookup k).getD [])[i]?).map Prod.fst = some x⌝ ∗
        vv.Value' ↦*□ x)) Hkv.2).1 $$ Hsls
    ihave %Hlen := ownSlice_len $$ Hvvs
    have Hlen' : vvs.length = ((resp !! key).getD []).length := by
      have := congrArg List.length Hver
      simpa using this
    ihave IH : iprop(∃ (j : w64) (itv : transport.ValueVersion) (lat'' : GMap GoString w64)
        (S'' : StoreS),
        "i" ∷ i_ptr ↦ j ∗ "item" ∷ item_ptr ↦ itv ∗
        "Hls" ∷ lockedState cfg γs n nbM latM h t nbrs lat'' S'' ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (vvs.length : Int)⌝ ∗
        "%Hm" ∷ ⌜∀ k, uint.Z (S'.maxCommitted k) ≤ uint.Z (S''.maxCommitted k)⌝ ∗
        "%Hb" ∷ ⌜respBelow resp S'' key (sint.Z j).toNat⌝) $$ [i item Hls]
    · iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, fun k => Int.le_refl _, fun j x v hj _ => ?_⟩
      exfalso; simp at hj
    wp_for IH
    wp_if_destruct
    · have Hlt : (sint.Z j).toNat < vvs.length := by word
      obtain ⟨vv, Hvv⟩ : ∃ vv, vvs[(sint.Z j).toNat]? = some vv :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj.1, Hif⟩]
      wp_apply wp_load_slice_index sl (sint.Z j) vvs (DFrac.own 1) vv Hj.1 $$ [Hvvs] as Hvvs
      · iframe; ipureintro; exact Hvv
      ihave ⟨%x, #Hx, %Hx⟩ := resp_entry resp key vvs _ vv Hvv Hver $$ Hvals
      ihave #Hve := resp_items_at cfg.γ resp key _ x vv.Version' Hx $$ Hitems
      ihave #Hcv := resp_committed_at cfg.γ resp key _ x vv.Version' Hx $$ Hcomm
      wp_apply (wp_commitM HL cfg n a (interface.ok e) γs nbM latM h t nbrs lat'' S'' key vv.Version')
        $$ [Hls]
      · iframe; iframe #
      iintro %err Hres
      cases hv : S''.hasVer key vv.Version'
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hres with ⟨#Herr, Hls⟩
        ihave %Hptr := errNotFound_ptr err $$ [Hspkg Herr]
        · iframe #
        obtain ⟨xe, rfl⟩ := Hptr
        ihave #Herr' := Herr
        iunfold errNotFound at Herr'
        icases Herr' with ⟨%xe', %Hxe', #Hga, -⟩
        wp_auto
        ihave ⟨HS, Hback⟩ := lockedState_store cfg γs n nbM latM h t nbrs lat'' S'' $$ Hls
        wp_apply (wp_store_Write cfg a γs e S'' key vv.Value' x vv.Version') $$ [$Hstore $Hinv $HS $Hx $Hve]
        iintro HS
        ihave Hls := Hback $$ %(S''.write key x vv.Version') HS
          %(StoreS.maxCommitted_write S'' key x vv.Version')
        wp_auto
        wp_apply (wp_commitM HL cfg n a (interface.ok e) γs nbM latM h t nbrs lat''
          (S''.write key x vv.Version') key vv.Version') $$ [Hls]
        · iframe; iframe #
        iintro %err2 Hres
        rw [hasVer_write_rp]
        simp only [↓reduceIte]
        icases Hres with ⟨%Herr2, %Hko2, #Hcv2, Hls⟩
        subst Herr2
        wp_auto
        wp_for_post
        iframe
        obtain ⟨hm1, hm2⟩ := mc_commit_ge _ key vv.Version' (hasVer_write_rp S'' key x vv.Version')
        iexists _, _, _, _
        iframe
        ipureintro
        refine ⟨⟨by word, by word⟩, fun k => ?_, fun j' x' v' hj' hl => ?_⟩
        · have := hm1 k; rw [StoreS.maxCommitted_write] at this; exact Int.le_trans (Hm k) this
        · have hjj : j' < (sint.Z j).toNat ∨ j' = (sint.Z j).toNat := by
            have : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
            omega
          rcases hjj with hjj | rfl
          · have := Hb j' x' v' hjj hl
            have h2 := hm1 key; rw [StoreS.maxCommitted_write] at h2
            exact Int.le_trans this h2
          · rw [Hx] at hl; cases hl; exact hm2
      · simp only [↓reduceIte]
        icases Hres with ⟨%Herr, %Hko, #Hcv', Hls⟩
        subst Herr
        wp_auto
        wp_for_post
        iframe
        obtain ⟨hm1, hm2⟩ := mc_commit_ge _ key vv.Version' hv
        iexists _, _, _, _
        iframe
        ipureintro
        refine ⟨⟨by word, by word⟩, fun k => Int.le_trans (Hm k) (hm1 k), fun j' x' v' hj' hl => ?_⟩
        have hjj : j' < (sint.Z j).toNat ∨ j' = (sint.Z j).toNat := by
          have : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
          omega
        rcases hjj with hjj | rfl
        · exact Int.le_trans (Hb j' x' v' hjj hl) (hm1 key)
        · rw [Hx] at hl; cases hl; exact hm2
    · ihave Hsls := Hclose $$ [Hvvs]
      · iexists vvs; iframe; iframe #; ipureintro; exact Hver
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _, _, _
      iframe
      have hjl : (sint.Z j).toNat = ((resp !! key).getD []).length := by
        rw [← Hlen']; word
      ipureintro
      refine ⟨fun k => Int.le_trans (Hmono k) (Hm k), fun j' k hj' hk => ?_⟩
      by_cases hji : j' = i.toNat
      · subst hji
        rw [Hkv.1] at hk; cases hk
        rw [← hjl]; exact Hb
      · exact respBelow_mono resp S' _ k _ Hm (Hdone j' k (by omega) hk)
  · iintro ⟨%lat', %S', %fk, %ky, Hls, forKey, key, Hn, Hsls, %Hmono, %Hdone⟩ Hmp
    wp_auto
    iapply HΦ $$ [Hls]
    · iexists lat', S'
      iframe
      ipureintro
      refine ⟨Hmono, fun _ k j x v hl => ?_⟩
      have hsome : (resp !! k).isSome = true := by
        cases hk : resp !! k with
        | none => rw [hk] at hl; simp at hl
        | some _ => rfl
      have hin : k ∈ keys := (Hkeys.1 k).2 ((Hdom k).2 hsome)
      obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.1 hin
      have hidxlt : idx < keys.length := by
        rcases (List.getElem?_eq_some_iff.1 hidx) with ⟨h1, _⟩; exact h1
      have hjlt : j < ((resp !! k).getD []).length := by
        rcases (List.getElem?_eq_some_iff.1 hl) with ⟨h1, _⟩; exact h1
      exact Hdone idx k (by rw [← Hkeys.2.1] at *; omega) hidx j x v hjlt hl
    ileft; ipureintro; rfl

theorem wp_requestFwdPropagation (HL : Laws (GF := GF)) :
    requestFwdPropagation.spec (GF := GF) (hG := hG) := by
  intro cfg n a st γs nbM latM h t nbrs lat S c ca
  iintro %Φ ⟨#Hpkg, #Hctx, #Hf, Hls, #Hc⟩ HΦ
  ihave #Hf' := Hf
  iunfold nodeFields at Hf'
  icases Hf' with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  ihave #Hstore' := Hstore
  iunfold isStore at Hstore'
  icases Hstore' with ⟨%e, %he, -⟩
  subst he
  wp_method_call
  wp_call
  ihave #Hc' := Hc
  iunfold isNodeClient at Hc'
  icases Hc' with ⟨%ec, ⟨%hec, %Hca⟩, #Hcs⟩
  subst hec
  wp_auto
  ihave ⟨HS, Hback⟩ := lockedState_store cfg γs n nbM latM h t nbrs lat S $$ Hls
  wp_apply (wp_store_AllDirty_own γs e (1 : Qp).half S) $$ [$Hstore $HS]
  iintro %sl HS Hsl
  iapply fupd_wp
  imod (store_keysOk cfg a γs S ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hinv $HS] with ⟨HS, %HSk⟩
  imodintro
  ihave Hls := Hback $$ %S HS %(fun _ => rfl)
  unfold itemsIn
  icases Hsl with ⟨%ps, %es, Hsl, %Hes, #Hps⟩
  wp_auto
  wp_apply (wp_propagateRequestFromItems sl ps es) $$ [$Hpkg $Hsl $Hps]
  iintro %ptr %req Hreq Hsl %Hreq %Hreqd
  wp_auto
  icases Hcs with ⟨-, -, -, -, -, -, Hfwd, -, -⟩
  wp_apply Hfwd $$ %(reqKeysOk_of S es req HSk (fun e he => (Hes.2 e he).1) Hreqd) Hreq
  iintro %rp %err Hres
  icases Hres with (⟨%Herr, Hreq, %resp, Hresp, #Hitems⟩ | #Herr)
  · subst Herr
    wp_auto
    wp_apply (wp_writePropagated cfg n a (interface.ok e) γs nbM latM h t nbrs lat S rp resp)
      $$ [Hls Hresp]
    · iframe; iframe #
    iintro %err2 Hls Herr2
    wp_auto
    iapply HΦ $$ Hls Herr2
  · ihave %Hok := errAny_ok err $$ Herr
    obtain ⟨ei, rfl⟩ := Hok
    wp_auto
    wp_log [GoInterface.ok ei]
    · iapply argOks1; iapply argOk_err $$ Herr
    iapply HΦ $$ [Hls]
    · iexists S; iexact Hls
    iright; iexact Herr

theorem wp_requestBackPropagation (HL : Laws (GF := GF)) :
    requestBackPropagation.spec (GF := GF) (hG := hG) := by
  intro cfg n a st γs nbM latM h t nbrs lat S c ca L
  iintro %Φ ⟨#Hpkg, #Hctx, #Hf, Hls, #Hc, #Hcov⟩ HΦ
  ihave #Hf' := Hf
  iunfold nodeFields at Hf'
  icases Hf' with ⟨%f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac, #Haddr, #Hpub, #Hcdra, #Hlog, #Hch,
    %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  ihave #Hstore' := Hstore
  iunfold isStore at Hstore'
  icases Hstore' with ⟨%e, %he, -⟩
  subst he
  wp_method_call
  wp_call
  ihave #Hc' := Hc
  iunfold isNodeClient at Hc'
  icases Hc' with ⟨%ec, ⟨%hec, %Hca⟩, #Hcs⟩
  subst hec
  wp_auto
  ihave ⟨HS, Hback⟩ := lockedState_store cfg γs n nbM latM h t nbrs lat S $$ Hls
  wp_apply (wp_store_AllCommitted_own γs e (1 : Qp).half S) $$ [$Hstore $HS]
  iintro %sl HS Hsl
  iapply fupd_wp
  imod (store_keysOk cfg a γs S ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hinv $HS] with ⟨HS, %HSk⟩
  imodintro
  ihave Hls := Hback $$ %S HS %(fun _ => rfl)
  unfold itemsIn
  icases Hsl with ⟨%ps, %es, Hsl, %Hes, #Hps⟩
  wp_auto
  wp_apply (wp_propagateRequestFromItems sl ps es) $$ [$Hpkg $Hsl $Hps]
  iintro %ptr %req Hreq Hsl %Hreq %Hreqd
  wp_auto
  icases Hcs with ⟨-, -, -, -, -, -, -, Hbck, -⟩
  wp_apply Hbck $$ %(reqKeysOk_of S es req HSk (fun e he => (Hes.2 e he).1) Hreqd) Hreq Hcov
  iintro %rp %err Hres
  icases Hres with (⟨%Herr, Hreq, %resp, Hresp, #Hitems, #Hcomm, %Hcovers⟩ | #Herr)
  · subst Herr
    wp_auto
    wp_apply (wp_commitPropagated HL cfg n a (interface.ok e) γs nbM latM h t nbrs lat S rp resp)
      $$ [Hls Hresp]
    · iframe; iframe #
    iintro %err2 ⟨%lat', %S', Hls, %Hmono, %Hall⟩ Herr2
    wp_auto
    iapply HΦ $$ [Hls] Herr2
    iexists lat', S'
    iframe
    ipureintro
    refine ⟨Hmono, fun hnil k => ?_⟩
    by_cases hlt : uint.Z (reqVer req k) < uint.Z (cvOf L k)
    · obtain ⟨x, v', hmem, hle⟩ := Hcovers k hlt
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem
      exact Int.le_trans hle (Hall hnil k j x v' hj)
    · rcases Hreq k with h0 | ⟨e0, he0, hk0, hv0⟩
      · rw [h0] at hlt; word
      · obtain ⟨hi, hc⟩ := (Hes.2 e0 he0)
        rw [show e0.2.2.2 = true from hc] at hi
        have hm := StoreS.maxCommitted_ub S e0.1 e0.2.2.1 e0.2.1
          ((StoreS.mem_items S e0.1 _).1 hi)
        rw [hk0, hv0] at hm
        have := Hmono k
        omega
  · ihave %Hok := errAny_ok err $$ Herr
    obtain ⟨ei, rfl⟩ := Hok
    wp_auto
    wp_log [GoInterface.ok ei]
    · iapply argOks1; iapply argOk_err $$ Herr
    iapply HΦ $$ [Hls]
    · iexists lat, S
      iframe
      ipureintro
      refine ⟨fun k => Int.le_refl _, fun h => ?_⟩
      cases h
    iright; iexact Herr

end reqprop

end NodeP

end github_com.despreston.go_craq

end Perennial
