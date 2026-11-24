/-
The proof of `Server.register` (`Net/Spec/net/rpc/Server__register.lean`): the codec's `Receiver`
(`rcvOk`), the name's checks (the premises exclude the logging ones), the methods copied into the
service's map (`wp_map_for_range`, each `*methodType` with its mutex), then the services map under
`mapLock`: a new name is inserted, with its ghost element made persistent.
-/
module

public import Net.Spec.net.rpc.Server__register
public import Net.Spec.net.rpc.getCodec
public import Net.Spec.go.token.IsExported
public import Net.Proof.net.rpc.Errs
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS] [sync.Assumptions] [errors.Assumptions] [go.token.Assumptions]

theorem keys_fresh {K : Type} (keys : List K) (i : Nat) (key : K) (hnd : keys.Nodup)
    (hk : keys[i]? = some key) : key ∉ keys.take i := by
  have h1 : key ∈ keys.drop i := by
    rw [List.getElem?_eq_some_iff] at hk
    obtain ⟨hi, rfl⟩ := hk
    exact List.mem_iff_getElem.2 ⟨0, by simp; omega, by simp⟩
  have hnd' := hnd
  rw [← List.take_append_drop i keys] at hnd'
  intro hm
  exact (List.nodup_append.1 hnd').2.2 key hm key h1 rfl

theorem take_succ_mem {K : Type} (keys : List K) (i : Nat) (key k : K) (hk : keys[i]? = some key)
    (h : k ∈ keys.take i ∨ k = key) : k ∈ keys.take (i + 1) := by
  rw [List.take_succ, hk]
  rcases h with h | h
  · exact List.mem_append_left _ h
  · subst h; simp

theorem Server.register.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_getCodec : getCodec.spec (GF := GF) (hG := hG))
    (wp_IsExported : go.token.IsExported.spec (GF := GF) (hG := hG)) :
    Server.register.spec (GF := GF) (hG := hG) := by
  intro s γ C rcvr S nm np name useName hname
  wp_start as ⟨#Hs, #Hset, Hrcv⟩
  wp_auto
  wp_apply wp_getCodec C $$ Hset as %cd #Hcd
  unfold codecIs
  icases Hcd with ⟨%v, #Hv, -, -, #Hrcvok⟩
  iStructNamed Hv
  wp_auto
  unfold rcvOk
  wp_bind (App (Val #v.Receiver') _)
  iapply Hrcvok $$ Hrcv
  inext
  iintro %rp #Hrp
  unfold rcvrIs
  icases Hrp with ⟨%rv, %M, #Hrv, %Hrf, #HM, #Hms⟩
  obtain ⟨Hnm, Hnp, HMs⟩ := Hrf
  iStructNamed Hrv
  wp_auto
  cases useName
  case' false =>
    simp only [regNameOk, Bool.false_eq_true, ite_false] at hname
    obtain ⟨hnp, c, rest, hnm, hc⟩ := hname
    subst hnp
    wp_auto
    rw [Hnp]
    wp_auto
    rw [Hnm, hnm]
    wp_auto
    wp_apply wp_IsExported c rest hc
    (try wp_auto)
    simp only [Bool.false_eq_true, ite_false]
    generalize c :: rest = sn
  case' true =>
    simp only [regNameOk, ite_true] at hname
    wp_auto
    rw [decide_eq_false hname]
    wp_auto
    simp only [ite_true]
    generalize name = sn

  all_goals
    wp_apply (wp_map_make1 (K := GoString) (V := Loc)) as %mp2 Hmp2
    (try wp_auto)
    wp_apply (wp_map_for_range (V := Loc) (fun keys (i : Int) => iprop(∃ M2 : GMap GoString Loc,
        mp2 ↦$ M2 ∗ ([∗map] m ↦ mt ∈ M2, methodTypeIs C rcvr (S m) mt) ∗
        s_ptr ↦ «$r0_ptr» ∗ «$r0_ptr» ↦ ({ name' := sn, rcvr' := rcvr, method' := mp2 } : net.rpc.service) ∗
        (∃ x : Loc, m_ptr ↦ x) ∗ (∃ y : GoString, mname_ptr ↦ y) ∗
        ⌜0 ≤ i ∧ GMap.size M2 = i.toNat ∧ ∀ k, (M2 !! k).isSome → k ∈ keys.take i.toNat⌝))
      _ go.string (go.GoType.PointerType net.rpc.Method.ty) rv.Methods' M DFrac.discard) $$ HM
    iintro %keys ⟨%Hkeys, %Hklen, %Hknd⟩
    isplitl [Hmp2 s «$r0» m mname]
    · iexists ∅
      iframe
      isplitl
      · iapply BigSepM.bigSepM_empty.2; iempintro
      ipureintro
      refine ⟨by omega, ?_, fun k h => ?_⟩
      · exact GMap.map_size_empty
      · simp [GMap.lookup_empty] at h
    isplitr
    · imodintro
      iintro %i %key %mm ⟨%Hik, %Hmm⟩ ⟨%M2, HM2, HMT, Hsp, Hr0, ⟨%x, Hm⟩, ⟨%y, Hmn⟩, %HP⟩
      obtain ⟨Hi0, HMsz, HMdom⟩ := HP
      wp_auto
      iStructNamed «$r0»
      ipersist m
      ihave #Hmok := BigSepM.bigSepM_lookup (by rw [gmap_get?_eq]; exact Hmm) $$ Hms
      imod sync.init_Mutex (∃ n : w64, structFieldRef net.rpc.methodType go!"numCalls" «$r0_ptr» ↦ n) ⊤
          (structFieldRef net.rpc.methodType go!"Mutex" «$r0_ptr») $$ Mutex [numCalls] with #Hmtx
      · inext; iexists _; iexact numCalls
      have Hfresh : M2 !! key = none := by
        cases h : M2 !! key with
        | none => rfl
        | some _ =>
          exfalso
          exact keys_fresh keys i.toNat key Hknd Hik (HMdom key (by simp [h]))
      (try simp only)
      wp_apply (wp_mapInsert go.string mp2 M2 key «$r0_ptr») $$ HM2 as HM2
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists M2.insert key «$r0_ptr»
      iframe HM2 Hsp Hr0
      isplitl [HMT]
      · iapply (BigSepM.bigSepM_insert (by rw [gmap_get?_eq]; exact Hfresh)).2
        iframe HMT
        iunfold methodTypeIs
        iexists mm
        iframe m Hmok Hmtx
      isplitl [Hm]
      · iexists _; iexact Hm
      isplitl [Hmn]
      · iexists _; iexact Hmn
      ipureintro
      refine ⟨by omega, ?_, fun k hk => ?_⟩
      · rw [GMap.map_size_insert_None _ _ _ Hfresh, HMsz]; omega
      · rw [show (i + 1).toNat = i.toNat + 1 by omega]
        apply take_succ_mem keys i.toNat key k Hik
        by_cases hkk : k = key
        · exact Or.inr hkk
        · left; apply HMdom; rwa [GMap.lookup_insert_ne _ _ (Ne.symm hkk)] at hk
    iintro ⟨%M2, HM2, HMT, Hsp, Hr0, -, -, %HP⟩ -
    obtain ⟨-, HM2sz, -⟩ := HP
    wp_auto
    wp_apply (wp_map_len_lt (K := GoString) (V := Loc) mp2 M2 (DFrac.own 1)) $$ HM2 as ⟨HM2, %HM2lt⟩
    have hsz : W64 (GMap.size M2) ≠ W64 0 := by
      rw [HM2sz]; simp only [Int.toNat_natCast]
      intro h
      apply HMs
      have := congrArg BitVec.toNat h
      simp [W64] at this
      rw [HM2sz] at HM2lt; simp only [Int.toNat_natCast] at HM2lt
      rw [Nat.mod_eq_of_lt (by omega)] at this
      exact this
    rw [decide_eq_false hsz]
    wp_auto
    iStructNamed Hr0
    ipersist rcvr
    ipersist method
    imod ownMap_persist mp2 (DFrac.own 1) M2 $$ HM2 with #HM2
    ihave #HMT := HMT
    iunfold isServer at Hs
    icases Hs with ⟨#Hsync, #Hmu, -, -⟩
    wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown, Hinv⟩
    iunfold svcMapInv at Hinv
    icases Hinv with ⟨%smp, %M3, Hsm, HM3, Hγ⟩
    wp_auto
    wp_apply (wp_map_lookup2 go.string (go.GoType.PointerType net.rpc.service.ty) smp M3 sn (DFrac.own 1)) $$ HM3 as HM3
    cases hl : M3 !! sn with
    | none =>
      simp only [Option.isSome_none, decide_false]
      wp_auto
      wp_apply (wp_mapInsert go.string smp M3 sn «$r0_ptr») $$ HM3 as HM3
      imod ghost_map_insert_persist sn «$r0_ptr» (by rw [← gmap_get?_eq]; exact hl) $$ Hγ with ⟨Hγ, #Hel⟩
      wp_apply wp_Unlock _ (svcMapInv γ s) $$ [$Hsync $Hmu $Hown Hsm HM3 Hγ]
      · iunfold svcMapInv
        iexists smp, _
        iframe Hsm HM3 Hγ
      (try wp_auto)
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iunfold svcReg
      iexists «$r0_ptr»
      iframe Hel
      iunfold svcIs
      iexists rcvr, mp2, M2
      iframe rcvr method HM2 HMT
    | some sv0 =>
      simp only [Option.isSome_some, _root_.decide_true]
      wp_auto
      wp_apply wp_Unlock _ (svcMapInv γ s) $$ [$Hsync $Hmu $Hown Hsm HM3 Hγ]
      · iunfold svcMapInv
        iexists smp, M3
        iframe Hsm HM3 Hγ
      (try wp_auto)
      wp_apply wp_errors_New' as %x #-
      iapply HΦ
      iright
      ipureintro; simp [interface.mkOk]

end proof

end net.rpc
end Perennial
