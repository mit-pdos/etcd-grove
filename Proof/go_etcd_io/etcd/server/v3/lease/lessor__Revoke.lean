/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Revoke.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Revoke
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Keys
public import Spec.sort.StringSlice__Sort
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeDeleteLease
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStoreTxnWrite__End
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Write
public import Batteries.Data.List.Perm
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriter

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem lease.lessor.Revoke.wp_proof
    (hKeys : lease.Lease.Keys.spec (GF := GF) (hG := hG))
    (hSort : sort.StringSlice.Sort.spec (GF := GF) (hG := hG))
    (hUDL : schema.UnsafeDeleteLease.spec (GF := GF) (hG := hG))
    (hDel : mvcc.metricsTxnWrite.DeleteRange.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.watchableStoreTxnWrite.End.spec (GF := GF) (hG := hG)) :
    lease.lessor.Revoke.spec (GF := GF) (hG := hG) := by
  intro lp γl id rd ws st γw log L d r P Pre Q Post f
  wp_start as ⟨#Hinv, %Hγ, Hro, #Hrd, Hrdr, Hwt, Hww, %Hlen, Hhook, Hcs, Hown, Hrvk, Hrb, Hbeon, #Hcok⟩
  obtain ⟨hγl, hkb⟩ := Hγ
  subst hγl
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hli : (leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hli with ⟨#Hnf, -, -, -, -, ⟨%crv, #Hcrv, #Hcrvs⟩, -, -⟩
  ihave #Hnf' := Hnf
  iunfold leaseErrVar at Hnf'
  icases Hnf' with ⟨%enf, #Henf, -⟩
  ihave #Hinv' := Hinv
  iunfold lessorInv at Hinv'
  icases Hinv' with ⟨%Hlp, #Hpin, #Hmu⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd0, %L', Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hls, Hx⟩
  iunfold leaseOwn at Hown
  icases Hown with ⟨Hfr, Hcls⟩
  ihave %Hag := leaseFrag_agree γw.st.leases _ _ _ _ $$ [$Hfr $Hg]
  subst Hag
  (try wp_auto)
  wp_apply (wp_map_lookup1 LeaseID.ty (go.GoType.PointerType Lease.ty) lm M id) $$ HM as HM
  cases hM : M.lookup id with
  | none =>
    -- not live: nothing changed
    have hnot : id ∉ L := by
      intro h; have := (HL id).1 h; rw [hM] at this; cases this
    simp only [Option.getD_none]
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx]
    · inext
      iunfold lessorMu
      iexists lm, im, M, I, rd0, L
      iframe
      iframe Hls
      ipureintro; exact HL
    (try wp_auto)
    iapply HΦ
    iframe Hro Hrdr Hhook Hbeon
    ileft
    iunfold mvcc.csContract at Hcs
    icases Hcs with ⟨HPre, -, -⟩
    iframe Hwt Hww HPre Hrb Hrvk
    isplitr
    · ipureintro; exact hnot
    isplitr
    · iexists enf; iframe Henf; ipureintro; rfl
    iunfold leaseOwn; iframe Hfr Hcls
  | some l =>
    simp only [Option.getD_some]
    have hidL : id ∈ L := (HL id).2 (by rw [hM]; rfl)
    ihave #Hlo := BigSepM.bigSepM_lookup hM $$ Hls
    ihave #Hlo' := Hlo
    iunfold isLeaseObj at Hlo'
    icases Hlo' with ⟨%Hnn, #Hlmu⟩
    simp only [Hnn, decide_false]
    -- the owner's closer of the lease (its element agrees with the lessor's map)
    iunfold leaseClosers at Hcls
    icases Hcls with ⟨%lp', %γga, %γcl, %C, %im', #Hp, %HC, Him', HI', %HIL, Hcm⟩
    icases lessorAuth_pin γw.st.leases 1 lp lp' L M γga γcl $$ [$Ha $Hp] with ⟨%Hlp', Hcl, Hback⟩
    subst Hlp'
    obtain ⟨l', hCl⟩ : ∃ l', C.lookup id = some l' := Option.isSome_iff_exists.1 ((HC id).1 hidL)
    icases closers_take γcl C id l' _ hCl $$ Hcm with ⟨Hcid, Hcw⟩
    iunfold closerAt at Hcid
    icases Hcid with ⟨He, Hio, Hslot⟩
    ihave %HMl := ghost_map_lookup $$ Hcl He
    rw [hM] at HMl
    injection HMl with HMl
    subst HMl
    -- the revokers' half of the element and the right to close `l.revokec`, kept until the end
    iunfold leaseRevokers at Hrvk
    icases Hrvk with ⟨%lp3, %γga3, %γcl3, %C3, #Hp3, %HC3, Hrs⟩
    ihave %Hpp := lessorPinG_agree _ lp lp3 γga γga3 γcl γcl3 $$ [$Hp $Hp3]
    obtain ⟨rfl, rfl, rfl⟩ := Hpp
    obtain ⟨l3, hC3l⟩ : ∃ l3, C3.lookup id = some l3 := Option.isSome_iff_exists.1 ((HC3 id).1 hidL)
    icases (BigSepM.bigSepM_delete (Φ := fun (i : w64) (x : Loc) =>
        iprop(ghostMapElem (GF := GF) γcl i (DFrac.own (1 : Qp).half) x ∗
          ∃ c : GoChan, lsF go!"revokec" x ↦□ c ∗ revokeCloser c)) hC3l).1 $$ Hrs
      with ⟨⟨Hre, %c, #Hrc, Hrcl⟩, Hrs⟩
    icombine He Hre gives %Hel
    obtain ⟨-, Hel⟩ := Hel
    subst Hel
    ihave Ha := Hback $$ %M Hcl
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx]
    · inext
      iunfold lessorMu
      iexists lm, im, M, I, rd0, L
      iframe
      iframe Hls
      ipureintro; exact HL
    -- `le.rd`, read with the deleter's owner's half: not `nil`
    iunfold rdOwn at Hro
    icases Hro with ⟨%lpr, #Hpinr, Hrof⟩
    ihave %Hlpr := lessorPin_agree γw.st.leases lp lpr $$ [$Hpin $Hpinr]
    subst Hlpr
    ihave #Hrd' := Hrd
    iunfold mvcc.rdIs at Hrd'
    icases Hrd' with ⟨%Hrdnn, #Hrdt⟩
    (try wp_auto)
    simp only [Hrdnn, decide_false]
    (try wp_auto)
    -- `txn := le.rd()`: the watchable store's write transaction, the hook run on `Pre`
    iunfold mvcc.csContract at Hcs
    icases Hcs with ⟨HPre, #Htr, Hupd⟩
    wp_apply Hrdt $$ %log %P %Pre %Q %f [$Hrdr $Hwt $Hww $Hhook $HPre $Htr] as %tw %trace ⟨⟨%crev, Htx⟩, HQ, Hhook⟩
    · ipureintro; exact Hlen.1
    (try wp_auto)
    -- `keys := l.Keys()`: the keys the owner's item map puts on `id`
    wp_apply (hKeys l (mvcc.leaseItemsOf (mvcc.stateAfter log)) id) $$ [$Hlo $Hslot $Hio]
      as %ksl %ks ⟨Hksl, Hslot, Hio, %Hks⟩
    ihave Hcm := Hcw $$ %(mvcc.leaseItemsOf (mvcc.stateAfter log)) %(fun _ _ _ => Iff.rfl)
      [He Hio Hslot]
    · iunfold closerAt; iframe He Hio Hslot
    ihave Hown : leaseOwn γw.st.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log)) $$ [Hfr Him' HI' Hcm]
    · iunfold leaseOwn; iframe Hfr
      iunfold leaseClosers
      iexists lp, γga, γcl, C, im'
      iframe Hp Him' HI' Hcm
      ipureintro; exact ⟨HC, HIL⟩
    (try wp_auto)
    -- `sort.StringSlice(keys).Sort()`: the keys are keys of the state, so few enough
    have hkst : ∀ k ∈ ks, k ∈ (mvcc.stateAfter log).map EtcdKv.key := by
      intro k hk
      have h := (Hks.1 k).1 hk
      rw [mvcc.leaseItemsOf_lookup] at h
      cases hf : mvcc.findKey k (mvcc.stateAfter log) with
      | none => simp only [hf] at h; cases h
      | some kv =>
        exact List.mem_map.2 ⟨kv, List.mem_of_find?_eq_some hf, mvcc.findKey_key hf⟩
    have hkslen : ks.length ≤ 2 ^ 62 := by
      have h := (List.subperm_of_subset Hks.2 hkst).length_le
      rw [List.length_map] at h
      exact Nat.le_trans h Hlen.2
    ihave #Hsortpkg : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
    · iPkgInit
    wp_apply (hSort ksl ks) $$ [$Hksl] as %ks' ⟨Hksl, %Hperm, %Hsorted⟩
    · ipureintro; exact hkslen
    have hnd' : ks'.Nodup := (List.Perm.nodup_iff Hperm).1 Hks.2
    -- the write transaction, opened: its batch transaction's wrapper, the inner transaction
    iunfold mvcc.isWatchTxnWrite at Htx
    iNamed Htx
    ihave #Hwrap : mvcc.twWrap (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStoreTxnWrite.ty) #tw mw $$ []
    · iunfold mvcc.twWrap; iright; iexists tw, ws; iframe Htw; ipureintro; exact ⟨rfl, rfl⟩
    ihave #Hnil : (slice.nil ↦*□ ([] : GoString) : IProp GF) $$ []
    · iapply (ownSlice_nil DFrac.discard)
    ihave %Hksl := ownSlice_len _ _ _ $$ Hksl
    -- `for _, key := range keys { txn.DeleteRange([]byte(key), nil) }`
    (try wp_auto)
    ihave IH : iprop(∃ (j : Nat) (kv0 : GoString) (dl : w64),
        "Hri" ∷ i_ptr ↦ (W64 (j : Int) : w64) ∗ "Hk" ∷ key_ptr ↦ kv0 ∗
        "%Hj" ∷ ⌜j ≤ ks'.length⌝ ∗
        "Htx" ∷ mvcc.isTxnWrite mw st γw.st trace log ((ks'.take j).map mvcc.Change.del)
          (W64 0) dl (W64 0) crev ∗
        "Hown" ∷ leaseOwn γw.st.leases L (mvcc.pendItems log ((ks'.take j).map mvcc.Change.del)))
        $$ [i key Htx Hown]
    · iexists 0, _, W64 0
      simp only [named, List.take_zero, List.map_nil]
      rw [show (W64 ((0 : Nat) : Int) : w64) = W64 0 from rfl,
        show mvcc.pendItems log [] = mvcc.leaseItemsOf (mvcc.stateAfter log) from rfl]
      iframe i key Htx Hown
      ipureintro; omega
    wp_for IH
    have hj : sint.Z (W64 (j : Int) : w64) = j := by
      have : j < 2 ^ 62 + 1 := by have := hkslen; have := Hperm.length_eq; omega
      unfold sint.Z W64
      rw [BitVec.toInt_ofInt_eq_self (by decide)
        (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
        (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
    have hkslZ : sint.Z ksl.len = ks'.length := by
      have h1 := Hksl.1; have h2 := Hksl.2; word
    wp_if_destruct
    · -- `i < len(keys)`: `txn.DeleteRange([]byte(keys[i]), nil)`
      have hlt : sint.Z (W64 (j : Int) : w64) < sint.Z ksl.len := by
        first | exact Hif | (have := go.intoVal_inj Hif; simpa using this)
      have hjlt : j < ks'.length := by rw [hj, hkslZ] at hlt; omega
      obtain ⟨kj, hkj⟩ : ∃ kj, ks'[j]? = some kj := ⟨_, List.getElem?_eq_getElem hjlt⟩
      have Hbnd : 0 ≤ sint.Z (W64 (j : Int) : w64) ∧ sint.Z (W64 (j : Int) : w64) < sint.Z ksl.len :=
        ⟨by rw [hj]; omega, hlt⟩
      simp only [Hbnd, _root_.and_self, ite_true]
      have hjN : (sint.Z (W64 (j : Int) : w64)).toNat = j := by rw [hj]; rfl
      wp_apply wp_load_slice_index ksl (sint.Z (W64 (j : Int) : w64)) ks' (DFrac.own 1) kj Hbnd.1
        $$ [$Hksl] as Hksl
      · ipureintro; rw [hjN]; exact hkj
      (try wp_auto)
      wp_apply (wp_string_to_bytes kj) as %ksb ⟨Hksb, -⟩
      imod ownSlice_persist _ _ _ $$ Hksb with #Hksb
      (try wp_auto)
      -- the key is in the pending state: on the lease, not deleted yet
      have hkjks : kj ∈ ks := Hperm.mem_iff.2 (List.mem_of_getElem? hkj)
      have hnot : kj ∉ ks'.take j := by
        intro hin
        obtain ⟨j', hj', hget⟩ := List.mem_iff_getElem.1 hin
        rw [List.getElem_take] at hget
        rw [List.length_take] at hj'
        have h1 : ks'[j']? = ks'[j]? := by
          rw [List.getElem?_eq_getElem (by omega), hget, hkj]
        have := (List.Nodup.getElem?_inj (by omega) hnd').1 h1
        omega
      have hpres : (mvcc.findKey kj (mvcc.applyChanges (W64 (log.length : Int)) (mvcc.stateAfter log)
          ((ks'.take j).map mvcc.Change.del))).isSome := by
        rw [mvcc.findKey_applyChanges_dels _ _ _ _ hnot]
        have h := (Hks.1 kj).1 hkjks
        rw [mvcc.leaseItemsOf_lookup] at h
        cases hf : mvcc.findKey kj (mvcc.stateAfter log) with
        | none => simp only [hf] at h; cases h
        | some _ => rfl
      ihave Htx : mvcc.isTxn mw st γw.st trace
          (.write log ((ks'.take j).map mvcc.Change.del) (W64 0) dl (W64 0)) crev $$ [Htx]
      · simp only [mvcc.isTxn]; iexact Htx
      ihave ⟨%Hok, Htx⟩ := txn.isTxn_kindOk mw st γw.st _ crev $$ Htx
      ihave Htx : mvcc.isTxnWrite mw st γw.st trace log ((ks'.take j).map mvcc.Change.del)
          (W64 0) dl (W64 0) crev $$ [Htx]
      · simp only [mvcc.isTxn]; iexact Htx
      ihave ⟨%Hfx, Htx⟩ := txn.isTxnWrite_facts mw st γw.st log _ _ _ _ crev $$ Htx
      have hdk : mvcc.delKeys log ((ks'.take j).map mvcc.Change.del) true kj [] = [kj] := by
        rw [txn.delKeys_eq log _ Hok.1 Hfx.1]
        unfold txn.srvSel txn.srvInRange
        simp only [↓reduceIte]
        rw [mvcc.filter_key_sorted kj _ (mvcc.applyChanges_sorted _ _ (mvcc.stateAfter_sorted log)),
          if_pos hpres]
      -- `txn.DeleteRange([]byte(key), nil)`
      wp_bind (App (App (Val #(methods _ _ _)) _) _)
      iapply mvcc.tw_wp2 _ _ mw go!"DeleteRange" (by unfold mvcc.twMethod; simp)
      iframe Hwrap
      wp_apply (hDel trace mw st γw.st log ((ks'.take j).map mvcc.Change.del) (W64 0) dl (W64 0)
          ksb slice.nil kj [] L crev) $$ [$Htx $Hksb $Hnil $Hown] as %n %rv ⟨Htx, Hown, -⟩
      try rw [show decide ((slice.nil : GoSlice) = slice.nil) = true from decide_eq_true rfl]
      rw [hdk]
      (try wp_auto)
      wp_for_post
      iframe
      iexists (j + 1), kj, _
      simp only [named]
      rw [List.take_add_one, hkj, Option.toList_some, List.map_append, List.map_singleton]
      rw [show (W64 ((j + 1 : Nat) : Int) : w64) = W64 (j : Int) + W64 1 by
        rw [← mvcc.W64_add_one]; simp]
      iframe
      ipureintro; omega
    · -- every key deleted
      have hge : ¬ sint.Z (W64 (j : Int) : w64) < sint.Z ksl.len := by
        first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
      have hjeq : j = ks'.length := by rw [hj, hkslZ] at hge; omega
      subst hjeq
      rw [List.take_length]
      -- the second critical section: the lessor's map still has `l` at `id` (the revokers' half)
      wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
      iunfold lessorMu at HR
      icases HR with ⟨%lm2, %im2, %M2, %I2, %rd2, %L2, Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL2, #Hls2, Hx⟩
      iunfold leaseOwn at Hown
      icases Hown with ⟨Hfr, Hcls⟩
      ihave %Hag := leaseFrag_agree _ _ _ _ _ $$ [$Hfr $Hg]
      subst Hag
      iunfold leaseClosers at Hcls
      icases Hcls with ⟨%lp4, %γga4, %γcl4, %C4, %im4, #Hp4, %HC4, Him4, HI4, %HIL4, Hcm⟩
      ihave %Hpp := lessorPinG_agree _ lp lp4 γga γga4 γcl γcl4 $$ [$Hp $Hp4]
      obtain ⟨rfl, rfl, rfl⟩ := Hpp
      icases lessorAuth_pin _ 1 lp lp L M2 γga γcl $$ [$Ha $Hp] with ⟨-, Hcl, Hback⟩
      obtain ⟨l4, hC4l⟩ : ∃ l4, C4.lookup id = some l4 :=
        Option.isSome_iff_exists.1 ((HC4 id).1 hidL)
      icases (BigSepM.bigSepM_delete (Φ := fun i x => closerAt (GF := GF) γcl
          (mvcc.pendItems log (ks'.map mvcc.Change.del)) i x) hC4l).1 $$ Hcm with ⟨Hc4, Hcm⟩
      iunfold closerAt at Hc4
      icases Hc4 with ⟨He4, -, -⟩
      icombine He4 Hre gives %Hel4
      obtain ⟨-, Hel4⟩ := Hel4
      subst Hel4
      ihave %HM2l := ghost_map_lookup $$ Hcl He4
      ihave He : ghostMapElem (GF := GF) γcl id (DFrac.own 1) l4 $$ [He4 Hre]
      · have h := (ghostMapElem_fractional (GF := GF) id γcl l4).fractional (1 : Qp).half (1 : Qp).half
        rw [Qp.half_add_half] at h
        iapply h.2; iframe
      imod ghost_map_delete $$ Hcl He with Hcl
      ihave Ha := Hback $$ %(M2.delete id) Hcl
      imod lessor_live_revoke _ lp L (M2.delete id) id $$ [$Ha $Hg $Hfr] with ⟨Ha, Hg, Hfr⟩
      iunfold lessorExtra at Hx
      icases Hx with ⟨%dc, %np, %h, %hx, %cp, %bl, Hdc, Hnp, Hnot, Hh, Hhq, Hcp, Hmeta, Hbl⟩
      icases (BigSepM.bigSepM_delete (Φ := fun i x => leaseMeta (GF := GF) i x 1) HM2l).1 $$ Hmeta
        with ⟨Hml, Hmeta⟩
      iunfold leaseMeta at Hml
      icases Hml with ⟨#HID, -, -, -, -, -⟩
      iunfold lessorBeOn at Hbeon
      icombine Hbl Hbeon gives %Hbb
      subst Hbb
      (try wp_auto)
      -- `delete(le.leaseMap, l.ID)`
      wp_apply (wp_mapDelete lm2 M2 id LeaseID.ty (go.GoType.PointerType Lease.ty)) $$ HM as HM
      -- the write transaction, packed: its batch transaction is the backend's
      ihave Hwtx : mvcc.isWatchTxnWrite tw ws st γw trace log (ks'.map mvcc.Change.del) (W64 0) dl
          (W64 0) crev $$ [Htx Htoks Hwlog]
      · iunfold mvcc.isWatchTxnWrite
        iexists mw
        simp only [named]
        iframe Htw Hws Htx Hcert Htoks Hwlog
      icases mvcc.isWatchTxnWrite_bt _ _ _ _ _ _ _ _ _ _ _ _ $$ Hwtx with ⟨Hwtx, %bt, #HbtB⟩
      have hbt : mvcc.storeBt (GF := GF) γw.st bt = mvcc.bkBt d.be bt := by
        unfold mvcc.storeBt mvcc.kbBt; rw [hkb]
      ihave #HbtB' : mvcc.bkBt d.be bt $$ []
      · rw [← hbt]; iexact HbtB
      iunfold mvcc.bkBt at HbtB'
      icases HbtB' with ⟨%t, %Hbtt, #Hfld, #HBT⟩
      subst Hbtt
      (try wp_auto)
      -- `le.b.BatchTx()`: the transaction's batch transaction (the backend's field)
      wp_apply HBT as %t' #Hfld'
      ihave %Htt := typedPointsto_agree_wand _ _ _ _ _ $$ Hfld Hfld'
      subst Htt
      (try wp_auto)
      -- `schema.UnsafeDeleteLease(tx, &leasepb.Lease{ID: l.ID})`: the delete under the KV write
      -- transaction's lock, of the lease's record, with the tracked buckets' right
      ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
      · iPkgInit
      ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hsch
      icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%bL, #HLeaseG, -⟩⟩
      wp_apply (hUDL ⟨go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty, #t⟩ «$a1_ptr» (DFrac.own 1) _ bL
          iprop(mvcc.isWatchTxnWrite tw ws st γw trace log (ks'.map mvcc.Change.del) (W64 0) dl (W64 0)
            crev ∗
            mvcc.storeRb γw.st r)
          iprop(mvcc.isWatchTxnWrite tw ws st γw trace log (ks'.map mvcc.Change.del) (W64 0) dl (W64 0)
            crev true ∗ mvcc.storeRb γw.st (mvcc.rbDel r mvcc.leaseName (u64Le id).reverse)))
        $$ [$«$a1» $Hwtx $Hrb] as ⟨-, Hwtx, Hrb⟩
      · iframe HLeaseG
        iintro !> %key %Φ' !> ⟨#Hkey, Hwtx, Hrb⟩ HΦ'
        icases mvcc.isWatchTxnWrite_leaseDel _ _ _ _ _ _ _ _ _ _ _ $$ Hwtx with ⟨%bt2, #HbtB2, Hd⟩
        ihave #Hb2 : mvcc.bkBt d.be bt2 $$ []
        · rw [← (show mvcc.storeBt (GF := GF) γw.st bt2 = mvcc.bkBt d.be bt2 by
            unfold mvcc.storeBt mvcc.kbBt; rw [hkb])]; iexact HbtB2
        iunfold mvcc.bkBt at Hb2
        icases Hb2 with ⟨%t2, %Hbt2, #Hfld2, -⟩
        subst Hbt2
        ihave %Ht2 := typedPointsto_agree_wand _ _ _ _ _ $$ Hfld Hfld2
        subst Ht2
        iapply Hd $$ %bL %key %_ %DFrac.discard %r %_ HLeaseG Hkey Hrb
        inext
        iintro Hwtx - Hrb
        iapply HΦ'
        iframe
      -- `txn.End()`: the deletes committed (the watchers notified), the batch lock's invariant
      -- back from the caller's update
      imod Hupd $$ HQ with ⟨HP, HPost⟩
      ihave #Hcn := Hcok $$ %(ks'.map mvcc.Change.del) %(by
        intro c hc; obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc; rfl)
      icases (mvcc.hookIs_split γw.st P f).1 $$ Hhook with ⟨#HhookOk, Hfrag⟩
      ihave Hhook : mvcc.hookIs γw.st P f $$ [Hfrag]
      · iapply (mvcc.hookIs_split γw.st P f).2; iframe HhookOk Hfrag
      wp_apply (hEnd trace tw ws st γw log (ks'.map mvcc.Change.del) (W64 0) dl (W64 0) P f crev true)
        $$ [$Hwtx $Hhook $HP $Hcn] as ⟨Hrdr, #Hcc, Hww, -, Hfrag⟩
      ihave Hhook : mvcc.hookIs γw.st P f $$ [Hfrag]
      · iapply (mvcc.hookIs_split γw.st P f).2; iframe HhookOk Hfrag
      (try wp_auto)
      -- `leaseRevoked.Inc()`
      iunfold counterSpec at Hcrvs
      icases Hcrvs with #Hcrvs
      wp_apply Hcrvs
      (try wp_auto)
      -- the deferred `le.mu.Unlock()`: the lessor without the lease
      have hfilt : ∀ x : w64, x ∈ L.filter (· != id) ↔ x ∈ L ∧ x ≠ id := by
        intro x; simp [List.mem_filter]
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hnot Hh Hhq Hcp
          Hmeta Hbl]
      · inext
        iunfold lessorMu
        iexists lm2, im2, (M2.delete id), I2, rd2, (L.filter (· != id))
        iframe Hlm HM Him HI Hrdf Ha Hg
        isplitr
        · ipureintro
          intro x
          rw [hfilt, HL2 x, GMap.lookup_delete_iff]
          by_cases hx : id = x
          · subst hx; simp
          · simp [hx, Ne.symm hx]
        isplitr
        · icases (BigSepM.bigSepM_delete (Φ := fun _ x => isLeaseObj (GF := GF) x) HM2l).1 $$ Hls2
            with ⟨-, #H⟩
          iexact H
        iunfold lessorExtra
        iexists dc, np, h, hx, cp, _
        iframe
      (try wp_auto)
      -- the deferred `close(l.revokec)`
      wp_apply (wp_revokec_close c) $$ [$Hrcl]
      (try wp_auto)
      iapply HΦ
      iframe Hrdr Hhook
      isplitl [Hrof]
      · iunfold rdOwn; iexists lp; iframe Hpin Hrof
      isplitl [Hbeon]
      · iunfold lessorBeOn; iexact Hbeon
      iright
      isplitr
      · ipureintro; exact ⟨hidL, rfl⟩
      iexists ks'
      isplitr
      · ipureintro
        refine ⟨hnd', fun k => (Hperm.mem_iff.symm).trans (Hks.1 k), Hsorted⟩
      iframe Hww HPost Hrb
      rw [txn.stateAfter_commitLog]
      isplitl [Hfr Him4 HI4 Hcm]
      · iunfold leaseOwn; iframe Hfr
        iunfold leaseClosers
        iexists lp, γga, γcl, (C4.delete id), im4
        iframe Hp Him4 HI4 Hcm
        ipureintro
        constructor
        · intro x
          rw [hfilt, HC4 x, GMap.lookup_delete_iff]
          by_cases hx : id = x
          · subst hx; simp
          · simp [hx, Ne.symm hx]
        · intro it id' hit
          rw [hfilt]
          refine ⟨HIL4 it id' hit, ?_⟩
          rintro rfl
          rw [mvcc.leaseItemsOf_dels] at hit
          by_cases hk : it.Key' ∈ ks'
          · rw [if_pos hk] at hit; cases hit
          · rw [if_neg hk] at hit
            apply hk
            apply Hperm.mem_iff.1
            apply (Hks.1 it.Key').2
            cases it; exact hit
      iunfold leaseRevokers
      iexists lp, γga, γcl, (C3.delete id)
      iframe Hp Hrs
      ipureintro
      intro x
      rw [hfilt, HC3 x, GMap.lookup_delete_iff]
      by_cases hx : id = x
      · subst hx; simp
      · simp [hx, Ne.symm hx]

end proof

end EtcdGrove
end Perennial
