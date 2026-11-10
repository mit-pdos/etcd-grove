/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__GetList.lean`: the prepared key, tracing
(no-ops), the list's items slice (`listContractOk'`), the read revision (`ValidateListOptions`),
then the range over `pagedChunks`' pages (`wp_forRange2`, `pagesOk`): each page's chunk goes to
`appendChunk`, the loop state is `chunkL` on the scope's prefix read so far (`ListPages`), and at the
loop's `break` it agrees with `kListL` (`kListL_agree`); then the continue token and `finalizeList`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__GetList
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__prepareKey
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__pagedChunks
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__appendChunk
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__finalizeList
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__validateMinimumResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.shouldStream
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.getNewItemFunc
public import Spec.k8s_io.apiserver.pkg.storage.ValidateListOptions
public import Spec.k8s_io.apiserver.pkg.storage.PrepareContinueToken
public import Spec.k8s_io.apimachinery.pkg.conversion.EnforcePtr
public import Spec.reflect.Value__Kind
public import Spec.reflect.Value__Len
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordStorageListMetrics
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordListLatency
public import Spec.k8s_io.component_base.tracing.Start
public import Spec.k8s_io.component_base.tracing.Span__End
public import Spec.go_opentelemetry_io.otel.attribute.String
public import Spec.go_opentelemetry_io.otel.attribute.Int
public import Spec.k8s_io.apiserver.pkg.audit.GetAuditIDTruncated
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ForRange
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListPages
public import Perennial.Proof.time.Link
public import Perennial.Proof.fmt.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- Naming a WP's postcondition (to refer to the code after a loop). -/
theorem wp_post_named (e : Expr) (Φ : val → IProp GF) :
    (∀ K : val → IProp GF, ⌜K = Φ⌝ -∗ WP e {{ K }}) ⊢ WP e {{ Φ }} := by
  iintro H
  iapply H $$ %Φ
  ipureintro; rfl

/-- `GetList`'s loop before page `i` (pure): the first page's state `σ` and revision `R` (`σ`'s, or
the past revision `R0` asked), the scope from page `i`'s start is the scope after its first `m`
key-values, the loop state `st` is `chunkL` on those, not full, and the counters are in range. -/
def pgFacts [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    {Obj : Type} [DecidableEq Obj] (c : StoreCfg GF Obj) (sel : Obj → Bool) (kp : GoString)
    (recur : Bool) (lim : Nat) (n R0 : w64) (σ : KVState) (R : w64) (i m : Nat)
    (st : k8s_etcd3.ListModel.LState w8 (Obj × Nat)) (nev : w64) : Prop :=
  R = (if uint.Z R0 = 0 then W64 (σ.rev : Int) else R0) ∧ uint.nat R ≤ σ.rev ∧
    σ.rev + 1 < 2 ^ 63 ∧ (uint.Z R0 = 0 → ¬ σ.rev < uint.nat n) ∧
    fromL (σ.at (uint.nat R)) kp recur (pagesL (σ.at (uint.nat R)) kp recur lim i).1 =
      (scopeL (σ.at (uint.nat R)) kp recur).drop m ∧
    m ≤ (scopeL (σ.at (uint.nat R)) kp recur).length ∧
    st = chunkL (fun x => sel x.1) lim ⟨[], none, false, 0⟩
      (decodedL c.S.dec ((scopeL (σ.at (uint.nat R)) kp recur).take m)) ∧
    st.more = false ∧ ¬ (0 < lim ∧ lim ≤ st.items.length) ∧
    0 ≤ sint.Z nev ∧ sint.nat nev ≤ m

theorem store.GetList.wp_proof
    [hKind : go.IsStrictlyComparable _root_.Perennial.reflect.Kind.underlying w64]
    (wp_prepareKey : store.prepareKey.spec (GF := GF) (hG := hG))
    (wp_pagedChunks : store.pagedChunks.spec (GF := GF) (hG := hG))
    (wp_appendChunk : store.appendChunk.spec (GF := GF) (hG := hG))
    (wp_finalizeList : store.finalizeList.spec (GF := GF) (hG := hG))
    (wp_validateMin : store.validateMinimumResourceVersion.spec (GF := GF) (hG := hG))
    (wp_shouldStream : shouldStream.spec (GF := GF) (hG := hG))
    (wp_getNewItemFunc : getNewItemFunc.spec (GF := GF) (hG := hG))
    (wp_ValidateListOptions : storage.ValidateListOptions.spec (GF := GF) (hG := hG))
    (wp_PrepareContinueToken : storage.PrepareContinueToken.spec (GF := GF) (hG := hG))
    (wp_EnforcePtr : conversion.EnforcePtr.spec (GF := GF) (hG := hG))
    (wp_Kind : reflect.Value.Kind.spec (GF := GF) (hG := hG))
    (wp_Len : reflect.Value.Len.spec (GF := GF) (hG := hG))
    (wp_RecordStorageListMetrics : metrics.RecordStorageListMetrics.spec (GF := GF) (hG := hG))
    (wp_RecordListLatency : metrics.RecordListLatency.spec (GF := GF) (hG := hG))
    (wp_Start : tracing.Start.spec (GF := GF) (hG := hG))
    (wp_End : tracing.Span.End.spec (GF := GF) (hG := hG))
    (wp_String : «attribute».String.spec (GF := GF) (hG := hG))
    (wp_Int : «attribute».Int.spec (GF := GF) (hG := hG))
    (wp_GetAuditIDTruncated : audit.GetAuditIDTruncated.spec (GF := GF) (hG := hG)) :
    store.GetList.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c L ci cd key opts lx rv0 cont0 rem0 k n sel emp Q P hQ hP
  wp_start as ⟨#Hst, %Hpre, #Hsel, #Hlc, #Hrs, #Hctx, #Hce, #Hnd, Htt, %htb, Hlx, HQ, #HP⟩
  obtain ⟨hk, hkl, hrv, hmatch, hcont, hn63, hlim⟩ := Hpre
  ihave #Hst0 := Hst
  iunfold isStore at Hst
  icases Hst with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt, #Hkc,
    #Hcl, #Hone, #Hregs, #Hcon, #Hlst⟩
  ihave #Hlst0 := Hlst
  iunfold storeListOk at Hlst
  icases Hlst with ⟨%af, %γp, #Faf, #Haf, -, %Hutf, %Hrp⟩
  ihave #Ptr : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing $$ []
  · iPkgInit
  ihave #Pat : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.«attribute» $$ []
  · iPkgInit
  ihave #Pau : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.audit $$ []
  · iPkgInit
  ihave #Pme : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics $$ []
  · iPkgInit
  ihave #Pti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Psg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  ihave #Pfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Pcv : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.conversion $$ []
  · iPkgInit
  ihave #Prf : isPkgInit (PROP := IProp GF) pkg_id.reflect $$ []
  · iPkgInit
  ihave #Pmeta : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» $$ []
  · iPkgInit
  ihave Fgr' := Fgr
  iStructNamed Fgr'
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_prepareKey sp c.resourcePrefix c.pathPrefix key opts.Recursive' $$ [] as %pk %perr %Hpk
  · iframe #
  rw [hk] at Hpk
  obtain ⟨rfl, rfl⟩ := Hpk
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfsl, -⟩
  wp_apply (_root_.Perennial.fmt.wp_Sprintf _ _ _ (DFrac.own 1) (by
    refine _root_.Perennial.fmt.ArgsWf.cons_other go.bool #opts.Recursive' _ ?_ ?_ ?_ .nil
    · simp [go.bool, go.string]
    · have hb : ¬ _root_.Perennial.fmt.IsIntType go.bool := by
        simp [_root_.Perennial.fmt.IsIntType, go.bool, go.int, go.int64, go.int32, go.int16,
          go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8]
      rintro (hi | ⟨hi, -⟩)
      · exact hb hi
      · rw [go.is_underlying] at hi; exact hb hi
    · exact Or.inr (Or.inl rfl)))
    $$ [$Hfsl] as %fname -
  (try wp_auto)
  wp_apply wp_GetAuditIDTruncated as %aid -
  wp_apply wp_String as %kv0 -
  wp_apply wp_String as %kv1 -
  (try wp_auto)
  wp_apply wp_String as %kv2 -
  (try wp_auto)
  wp_apply wp_String as %kv3 -
  (try wp_auto)
  wp_apply wp_Int as %kv4 -
  (try wp_auto)
  wp_apply wp_String as %kv5 -
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply wp_Start ci cd _ _ $$ [] as %ci' %spn ⟨%Hspn, #Hctx', #Hce', #Hnd'⟩
  · iframe #
  ihave #Hnd2 := Hnd' $$ Hnd
  iunfold ListSpec.listAt at Hlx
  icases Hlx with ⟨%pl, %Hlxe, Hli⟩
  subst Hlxe
  iunfold ListSpec.listAtItems at Hli
  icases Hli with ⟨%Hpl, %s0, Hip, Hits, Hmeta⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hip with ⟨Hip, %Hipn⟩
  ihave #Hlc' := Hlc
  iunfold listContractOk at Hlc'
  icases Hlc' with ⟨#Hrefl, #Hdecl, #Hupd, %Hnu⟩
  ihave #Hrefl' := Hrefl
  iunfold listContractOk' at Hrefl'
  icases Hrefl' with ⟨#HGI, #HMk0, #HMk, #HApp⟩
  (try wp_auto)
  wp_bind (App (Val _) (Val #(interface.mkOk (go.GoType.PointerType L.listTy) #pl : GoInterface)))
  iapply HGI $$ %pl %_ %Hpl
  inext
  (try wp_auto)
  wp_apply (wp_EnforcePtr (go.GoType.SliceType c.S.objTy) (L.itemsRef pl)) $$ [] as %rv %rerr %Hre
  · iframe #
    ipureintro; exact Hipn
  obtain ⟨rfl, Hrv⟩ := Hre
  (try wp_auto)
  wp_apply (wp_Kind v_ptr _ rv c.S.objTy (L.itemsRef pl)) $$ [$v] as v
  · iframe #
    ipureintro; exact Hrv
  (try wp_auto)
  ihave #Hcon' := Hcon
  iunfold contractOk at Hcon'
  icases Hcon' with ⟨%HtyOk, -, #Hver, -⟩
  wp_apply (wp_getNewItemFunc Obj c.S L pl rv) $$ [] as %nf #Hnf
  · iframe #
    ipureintro; exact ⟨HtyOk, Hnu, Hrv⟩
  (try wp_auto)
  wp_apply (wp_ValidateListOptions Obj c.S (c.pathPrefix ++ k) c.vi opts n hcont hrv hmatch) $$ []
  · iframe #
  (try wp_auto)
  wp_apply _root_.Perennial.time.wp_Now as %t0 -
  (try wp_auto)
  wp_bind (App (Val #af) _)
  ihave #Haf' := Haf
  iunfold aggrFactoryOk at Haf'
  iapply Haf'
  inext
  iintro %ag Hag
  (try wp_auto)
  have hrev0 : 0 ≤ sint.Z (listRevL opts.ResourceVersionMatch' opts.Recursive'
      opts.Predicate'.Limit' n) := by
    unfold listRevL; split
    · word
    · split <;> word
  have hrk : ∃ k', prepareKeyM c.resourcePrefix c.resourcePrefix false = some k' ∧
      (c.pathPrefix ++ k').length ≤ opKeyMax := by
    refine ⟨c.resourcePrefix, Hrp, ?_⟩
    have := (prepareKeyM_prefix c.pathPrefix c.resourcePrefix key k opts.Recursive' hk).length_le
    omega
  wp_apply (wp_pagedChunks Obj sp c ci' cd (c.pathPrefix ++ k) opts _ _ Q P hkl hrev0 hlim hcont
      hrk hQ hP) $$ [] as %chf Hpages
  · iframe #
    ipureintro; exact htb
  (try wp_auto)
  wp_apply (wp_shouldStream opts Obj c.S sel emp) $$ []
  · iframe #
  (try wp_auto)
  ipersist s
  ipersist listObj
  ipersist opts
  ipersist keyPrefix
  ipersist ctx
  ipersist paging
  ipersist newItemFunc
  ipersist streamed
  ipersist startTime
  ipersist aggregator
  generalize hR0 : listRevL opts.ResourceVersionMatch' opts.Recursive' opts.Predicate'.Limit' n = R0
    at hrev0
  wp_bind (App (App (Val (func.forRange 2)) _) _)
  iapply wp_post_named
  iintro %K %hK
  obtain ⟨HkP, hHkP⟩ : ∃ X : IProp GF, X = iprop(iprop(
      ∀ (σ : KVState) (R wr : w64) (lkp : GoSlice) (lkb : GoString) (hmv : Bool) (cnt nfch nev : w64)
        (e : GoInterface) (sl : GoSlice) (st : k8s_etcd3.ListModel.LState w8 (Obj × Nat)),
        «$res0_ptr» ↦ GoInterface.nil -∗ withRev_ptr ↦ wr -∗ lastKey_ptr ↦ lkp -∗ lkp ↦*□ lkb -∗
        hasMore_ptr ↦ hmv -∗ count_ptr ↦ cnt -∗ numFetched_ptr ↦ nfch -∗ numEvald_ptr ↦ nev -∗
        err_ptr ↦ e -∗ v_ptr ↦ rv -∗ L.itemsRef pl ↦ sl -∗ L.itemsAt sl (itemsOf c st) -∗
        □ Q (W64 (σ.rev : Int)) σ -∗ threadTok -∗
        ⌜R = (if uint.Z R0 = 0 then W64 (σ.rev : Int) else R0) ∧ uint.nat R ≤ σ.rev ∧
          σ.rev + 1 < 2 ^ 63 ∧ (uint.Z R0 = 0 → ¬ σ.rev < uint.nat n) ∧ wr = R ∧
          st.items = (kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k)
            opts.Recursive' (σ.at (uint.nat R))).items ∧
          hmv = (kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k)
            opts.Recursive' (σ.at (uint.nat R))).more ∧
          (hmv = true → (kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k)
            opts.Recursive' (σ.at (uint.nat R))).last = some lkb ∧ c.pathPrefix ++ k <+: lkb) ∧
          (hmv = true → emp = true → cnt = W64 ((kListL c.S.dec sel (limN opts.Predicate'.Limit')
            (c.pathPrefix ++ k) opts.Recursive' (σ.at (uint.nat R))).total : Int)) ∧
          0 ≤ sint.Z nfch ∧ 0 ≤ sint.Z nev⌝ -∗
        K executeVal) ∧
    iprop(∀ (e : GoInterface) (nfch nev : w64) (sl : GoSlice) (os : List (Obj × GoString)),
        «$res0_ptr» ↦ e -∗ numFetched_ptr ↦ nfch -∗ numEvald_ptr ↦ nev -∗ v_ptr ↦ rv -∗
        L.itemsRef pl ↦ sl -∗ L.itemsAt sl os -∗ threadTok -∗ ⌜0 ≤ sint.Z nfch ∧ 0 ≤ sint.Z nev⌝ -∗
        (listErr c e ∨ ∃ σ : KVState, □ Q (W64 (σ.rev : Int)) σ ∗ apierrors.tooLargeErrIs e ∗
          ⌜if uint.Z R0 = 0 then σ.rev < uint.nat n else σ.rev < uint.nat R0⌝) -∗
        K (returnVal #()))) := ⟨_, rfl⟩
  ihave Hk : (HkP) $$ [HΦ Hmeta Hag defer]
  · rw [hHkP]
    isplit
    · sorry
    · iintro %e %nfch %nev %sl %os «$res0» numFetched numEvald v Hip Hits Htt %Hnn Herr
      rw [hK]
      simp only
      wp_auto
      icases persistent_entails_left (L.itemsAt_wf _ _) $$ Hits with ⟨Hits, %Hiw⟩
      wp_apply (wp_Len v_ptr _ _ rv c.S.objTy (L.itemsRef pl) sl) $$ [$v $Hip] as ⟨v, Hip⟩
      · iframe #
        ipureintro; exact Hrv
      (try wp_auto)
      wp_apply (wp_RecordStorageListMetrics c.gr [] nfch nev sl.len Hnn.1 Hnn.2 Hiw.1 Hutf.1 Hutf.2
        (by decide))
      (try wp_auto)
      wp_apply (wp_RecordListLatency c.gr _ t0 Hutf.1 Hutf.2)
      (try wp_auto)
      wp_apply wp_End spn _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      iapply HΦ
      iframe Htt
      icases Herr with (#Herr | ⟨%σ, #HQσ, #Herr, %Hlt⟩)
      · ileft
        iframe Herr
        iexists os, rv0, cont0, rem0
        unfold ListSpec.listAt ListSpec.listAtItems
        iexists pl
        iframe
        ipureintro; exact ⟨rfl, Hpl⟩
      · iright
        iexists σ
        iframe HQσ
        by_cases h0 : uint.Z R0 = 0
        · rw [if_pos h0] at Hlt
          rw [if_pos h0, if_pos Hlt]
          iframe Herr
          iexists os, rv0, cont0, rem0
          unfold ListSpec.listAt ListSpec.listAtItems
          iexists pl
          iframe
          ipureintro; exact ⟨rfl, Hpl⟩
        · rw [if_neg h0] at Hlt
          rw [if_neg h0, if_pos Hlt]
          iframe Herr
          iexists os, rv0, cont0, rem0
          unfold ListSpec.listAt ListSpec.listAtItems
          iexists pl
          iframe
          ipureintro; exact ⟨rfl, Hpl⟩
  iapply wp_forRange2 _ _ _ (by simp) rfl
  iintro %y %Tok %Done HTok #Hy
  iunfold pagesOk at Hpages
  ispecialize Hpages $$ %y
    %(fun (o : Option (KVState × w64)) (i : Nat) => iprop(∃ (wr : w64) (lkp : GoSlice)
      (lkb : GoString) (hmv : Bool) (cnt nev : w64) (m : Nat) (e chE : GoInterface)
      (chv : k8s_io.apiserver.pkg.storage.etcd3.listChunk) (sl : GoSlice)
      (st : k8s_etcd3.ListModel.LState w8 (Obj × Nat)),
      Tok ∗ HkP ∗ «$res0_ptr» ↦ GoInterface.nil ∗ withRev_ptr ↦ wr ∗ lastKey_ptr ↦ lkp ∗
      lkp ↦*□ lkb ∗ hasMore_ptr ↦ hmv ∗ count_ptr ↦ cnt ∗ numFetched_ptr ↦ W64 (m : Int) ∗
      numEvald_ptr ↦ nev ∗ err_ptr ↦ e ∗ chunk_ptr ↦ chv ∗ chunkErr_ptr ↦ chE ∗ v_ptr ↦ rv ∗
      L.itemsRef pl ↦ sl ∗ L.itemsAt sl (itemsOf c st) ∗
      (match o with
       | none => iprop(⌜i = 0 ∧ wr = R0 ∧ m = 0 ∧ st = ⟨[], none, false, 0⟩ ∧ nev = W64 0⌝)
       | some (σ, R) => iprop(□ Q (W64 (σ.rev : Int)) σ ∗
          ⌜1 ≤ i ∧ wr = R ∧ pgFacts c sel (c.pathPrefix ++ k) opts.Recursive'
            (limN opts.Predicate'.Limit') n R0 σ R i m st nev ∧ emp = false ∧
            pageMore (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive'
              (limN opts.Predicate'.Limit') (i - 1) = true⌝))))
    %(fun w => iprop(⌜w.isPanic = false⌝ ∗ ((Tok ∗ K executeVal) ∨ (Done breakVal ∗ K executeVal) ∨
      ∃ r, Done (returnVal r) ∗ K (returnVal r))))
  iapply Hpages $$ Htt HQ HP [HTok Hk «$res0» withRev lastKey hasMore count numFetched numEvald err chunk
    chunkErr v Hip Hits] [] [] []
  · -- the state before the first page
    ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    simp only
    iexists R0, slice.nil, [], false, W64 0, W64 0, 0, GoInterface.nil, GoInterface.nil, _, s0,
      ⟨[], none, false, 0⟩
    iframe
    simp only [itemsOf, List.reverse_nil, List.map_nil]
    iframe
    isplitl []
    · iexact Hnil
    ipureintro
    simp
  · -- a page
    sorry
  · -- an error
    sorry
  · -- the end: after a page with more, `f` does not return
    iintro %σ %R %i HJ %Hpm
    simp only
    icases HJ with ⟨%wr, %lkp, %lkb, %hmv, %cnt, %nev, %m, %e, %chE, %chv, %sl, %st, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, %Hj⟩
    obtain ⟨-, -, -, -, Hm⟩ := Hj
    simp only [Nat.add_sub_cancel] at Hm
    rw [Hm] at Hpm
    cases Hpm

end proof

end k8s
end EtcdGrove
end Perennial
