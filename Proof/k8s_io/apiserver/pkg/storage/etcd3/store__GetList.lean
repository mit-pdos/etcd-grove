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
public import Spec.reflect.KindCompare
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

set_option maxHeartbeats 8000000 in
theorem store.GetList.wp_proof
    (wp_KindCompare : reflect.KindCompare.spec (GF := GF) (hG := hG))
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
  have hKind : go.IsStrictlyComparable _root_.Perennial.reflect.Kind.underlying w64 := wp_KindCompare
  intro _ _ Obj _ sp c L ci cd key opts lx rv0 cont0 rem0 k n sel emp Q P hQ hP hnr
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
      hrk hQ hP (by have := prepareKeyM_ne_nil _ _ _ _ hk; simp [this]) hnr) $$ [] as %chf Hpages
  · iframe #
    ipureintro; exact htb
  (try wp_auto)
  wp_apply (wp_shouldStream opts Obj c.S sel emp) $$ []
  · iframe #
  (try wp_auto)
  ipersist s
  ipersist listObj
  ipersist opts
  ihave #opts' := opts
  iStructNamed opts'
  ihave #Predicate' := Predicate
  iStructNamed Predicate'
  ipersist keyPrefix
  ipersist ctx
  ipersist paging
  ipersist newItemFunc
  ipersist streamed
  ipersist startTime
  ipersist aggregator
  generalize hR0 : listRevL opts.ResourceVersionMatch' opts.Recursive' opts.Predicate'.Limit' n = R0
    at hrev0
  have hR0n : uint.Z R0 ≠ 0 → R0 = n := by
    intro h
    rw [← hR0] at h ⊢
    unfold listRevL at h ⊢
    by_cases h1 : opts.ResourceVersionMatch' = go!"Exact"
    · rw [if_pos h1]
    · rw [if_neg h1] at h ⊢
      by_cases h2 : (opts.ResourceVersionMatch' = [] ∧ opts.Recursive' = true ∧
          0 < sint.Z opts.Predicate'.Limit' ∧ 0 < uint.Z n)
      · rw [if_pos h2]
      · rw [if_neg h2] at h; exact absurd (by simp) h
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
        (listErr c e ∨ ∃ (R' : w64) (σ : KVState), □ Q R' σ ∗ apierrors.tooLargeErrIs e ∗
          ⌜if uint.Z R0 = 0 then σ.rev < uint.nat n else σ.rev < uint.nat R0⌝) -∗
        K (returnVal #()))) := ⟨_, rfl⟩
  ihave Hk : (HkP) $$ [HΦ Hmeta Hag defer]
  · rw [hHkP]
    isplit
    · iintro %σ %R %wr %lkp %lkb %hmv %cnt %nfch %nev %e %sl %st «$res0» withRev lastKey #Hlkb hasMore
        count numFetched numEvald err v Hip Hits #HQσ Htt %Hf
      obtain ⟨hR, hRle, hσb, hRn, hwr, hit, hhm, hlast, hcnt, hnf, hne⟩ := Hf
      subst wr
      rw [hK]
      simp only
      wp_auto
      wp_apply (wp_bytes_to_string lkp lkb) $$ [$Hlkb] as -
      (try wp_auto)
      wp_apply (wp_PrepareContinueToken Obj c.S lkb (c.pathPrefix ++ k) R cnt hmv opts sel emp) $$ []
        as %t %rem %perr Hpct
      · iframe #
      have hkpne : c.pathPrefix ++ k ≠ [] := by
        have := prepareKeyM_ne_nil _ _ _ _ hk
        intro h; exact this (List.append_eq_nil_iff.1 h).2
      ihave Hpc : (⌜perr = GoInterface.nil ∧
          t = (if hmv then k8s_etcd3.encL (lkb ++ [W8 0]) (c.pathPrefix ++ k) R else [])⌝ ∗
          remIs rem (if hmv ∧ emp then some (cnt - opts.Predicate'.Limit') else none)) $$ [Hpct]
      · cases hmv
        · simp only [Bool.false_eq_true, ↓reduceIte, _root_.false_and]
          icases Hpct with %Hp
          obtain ⟨rfl, rfl, rfl⟩ := Hp
          simp only [remIs]
          ipureintro; simp
        · have henc : k8s_etcd3.encOkL (lkb ++ [W8 0]) (c.pathPrefix ++ k) = true := by
            unfold k8s_etcd3.encOkL
            exact decide_eq_true ⟨hkpne, (hlast rfl).2.trans (List.prefix_append _ _)⟩
          simp only [↓reduceIte, _root_.true_and, henc]
          cases emp
          · simp only [Bool.false_eq_true, ↓reduceIte]
            icases Hpct with ⟨%Hp, %Hr⟩
            simp only [remIs]
            ipureintro; exact ⟨⟨Hp.1, Hp.2⟩, Hr⟩
          · simp only [↓reduceIte]
            icases Hpct with ⟨%Hp, Hr⟩
            simp only [remIs]
            iframe Hr
            ipureintro; exact Hp
      icases Hpc with ⟨%Hpc, Hrem⟩
      obtain ⟨rfl, rfl⟩ := Hpc
      (try wp_auto)
      wp_apply (wp_finalizeList Obj sp c L _ pl opts.Predicate' sel emp R _ rem _ ag rv (itemsOf c st)
        rv0 cont0 rem0 rfl) $$ [Hag Hip Hits Hmeta Hrem] as Hlx
      · iframe # Hag Hrem
        isplitr
        · ipureintro; exact Hrv
        unfold ListSpec.listAtItems
        iframe
        ipureintro; exact Hpl
      unfold ListSpec.listAt ListSpec.listAtItems
      icases Hlx with ⟨%pl', %Hpl', -, %sl', Hip, Hits, Hmeta⟩
      have hpl : pl' = pl := by
        have h := ((interface_mkOk_inj _ _ _ _).1 Hpl').2
        exact (go.intoVal_inj h).symm
      subst hpl
      (try wp_auto)
      icases persistent_entails_left (L.itemsAt_wf _ _) $$ Hits with ⟨Hits, %Hiw⟩
      wp_apply (wp_Len v_ptr _ _ rv c.S.objTy (L.itemsRef pl') sl') $$ [$v $Hip] as ⟨v, Hip⟩
      · iframe #
        ipureintro; exact Hrv
      (try wp_auto)
      wp_apply (wp_RecordStorageListMetrics c.gr [] nfch nev sl'.len hnf hne Hiw.1 Hutf.1 Hutf.2
        (by decide))
      (try wp_auto)
      wp_apply (wp_RecordListLatency c.gr _ t0 Hutf.1 Hutf.2)
      (try wp_auto)
      wp_apply wp_End spn _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      have hσr : uint.nat (W64 (σ.rev : Int)) = σ.rev := by word
      have hcont' : (if (kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k)
            opts.Recursive' (σ.at (uint.nat R))).more then
          k8s_etcd3.encL ((kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k)
            opts.Recursive' (σ.at (uint.nat R))).last.getD [] ++ [W8 0]) (c.pathPrefix ++ k) R
          else []) = (if hmv then k8s_etcd3.encL (lkb ++ [W8 0]) (c.pathPrefix ++ k) R else []) := by
        rw [← hhm]
        cases hmv
        · rfl
        · simp [(hlast rfl).1]
      have hrem' : (if (kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k)
            opts.Recursive' (σ.at (uint.nat R))).more ∧ emp then
          some (W64 ((kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k)
            opts.Recursive' (σ.at (uint.nat R))).total : Int) - opts.Predicate'.Limit') else none) =
          (if hmv ∧ emp then some (cnt - opts.Predicate'.Limit') else none) := by
        rw [← hhm]
        cases hmv
        · simp
        · cases emp
          · simp
          · simp [hcnt rfl rfl]
      have hits' : (kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k)
            opts.Recursive' (σ.at (uint.nat R))).items.reverse.map
            (fun x => (x.1, c.S.fmtRV (W64 (x.2 : Int)))) = itemsOf c st := by
        rw [itemsOf, hit]
      iapply HΦ
      iframe Htt
      iright
      iexists (W64 (σ.rev : Int)), σ
      iframe HQσ
      isplitr
      · ipureintro; exact Or.inr rfl
      by_cases h0 : uint.Z R0 = 0
      · rw [if_pos h0] at hR
        rw [if_pos h0, if_neg (hRn h0), ← hR,
          show σ.store = σ.at (uint.nat R) by rw [hR, hσr]; rfl]
        isplitr
        · ipureintro; rfl
        unfold listIs ListSpec.listAt ListSpec.listAtItems
        rw [hcont', hrem', hits']
        iexists pl'
        iframe
        ipureintro; exact ⟨rfl, Hpl⟩
      · rw [if_neg h0] at hR
        have hle : ¬ σ.rev < uint.nat R0 := by rw [← hR]; omega
        rw [if_neg h0, if_neg hle, ← hR]
        isplitr
        · ipureintro; rfl
        unfold listIs ListSpec.listAt ListSpec.listAtItems
        rw [hcont', hrem', hits']
        iexists pl'
        iframe
        ipureintro; exact ⟨rfl, Hpl⟩
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
      icases Herr with (#Herr | ⟨%R', %σ, #HQσ, #Herr, %Hlt⟩)
      · ileft
        iframe Herr
        iexists os, rv0, cont0, rem0
        unfold ListSpec.listAt ListSpec.listAtItems
        iexists pl
        iframe
        ipureintro; exact ⟨rfl, Hpl⟩
      · iright
        iexists R', σ
        iframe HQσ
        isplitr
        · ipureintro
          left
          by_cases h0 : uint.Z R0 = 0
          · rw [if_pos h0] at Hlt; exact Hlt
          · rw [if_neg h0] at Hlt; rw [← hR0n h0]; exact Hlt
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
    iintro !> %σ %R %i %ch HJ Hfirst Hch
    simp only
    icases HJ with ⟨%wr, %lkp, %lkb, %hmv, %cnt, %nev, %m, %e0, %chE, %chv, %sl, %st, HTok, Hk,
      «$res0», withRev, lastKey, #Hlkb, hasMore, count, numFetched, numEvald, err, chunk, chunkErr, v,
      Hip, Hits, Ho⟩
    ihave ⟨#HQσ, %HU⟩ : (□ Q (W64 (σ.rev : Int)) σ ∗
        ⌜R = (if uint.Z R0 = 0 then W64 (σ.rev : Int) else R0) ∧ uint.nat R ≤ σ.rev ∧
          fromL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive'
            (pagesL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive'
              (limN opts.Predicate'.Limit') i).1 =
            (scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive').drop m ∧
          m ≤ (scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive').length ∧
          st = chunkL (fun x => sel x.1) (limN opts.Predicate'.Limit') ⟨[], none, false, 0⟩
            (decodedL c.S.dec ((scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k)
              opts.Recursive').take m)) ∧
          st.more = false ∧ ¬ (0 < limN opts.Predicate'.Limit' ∧
            limN opts.Predicate'.Limit' ≤ st.items.length) ∧
          0 ≤ sint.Z nev ∧ sint.nat nev ≤ m ∧
          (i = 0 → wr = R0 ∧ m = 0) ∧
          (i ≠ 0 → wr = R ∧ emp = false ∧ (uint.Z R0 = 0 → ¬ σ.rev < uint.nat n))⌝) $$ [Hfirst Ho]
    · cases i with
      | zero =>
        simp only [↓reduceIte]
        icases Hfirst with ⟨#HQσ, %Hf⟩
        icases Ho with %Ho
        obtain ⟨-, rfl, rfl, rfl, rfl⟩ := Ho
        iframe HQσ
        ipureintro
        refine ⟨Hf.1, Hf.2, ?_, Nat.zero_le _, rfl, rfl, fun h => by have h2 := h.2; simp at h2; omega,
          by decide, by decide, fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩
        simp only [pagesL, List.drop_zero]
        exact fromL_kp _ _ _
      | succ j =>
        simp only [Nat.succ_ne_zero, ↓reduceIte]
        icases Ho with ⟨#HQσ, %Ho⟩
        obtain ⟨-, hwr, Hpg, hemp, -⟩ := Ho
        obtain ⟨h1, h2, -, h4, h5, h6, h7, h8, h9, h10, h11⟩ := Hpg
        iframe HQσ
        ipureintro
        exact ⟨h1, h2, h5, h6, h7, h8, h9, h10, h11, fun h => by simp at h,
          fun _ => ⟨hwr, hemp, h4⟩⟩
    obtain ⟨hR, hRle, hfrom, hm, hst, hstm, hstf, hnev0, hnev, hi0, hi1⟩ := HU
    ihave %Hwf := (hQ _ σ) $$ HQσ
    obtain ⟨⟨-, -, -, hσb⟩, hwh, hks⟩ := Hwf
    change σ.rev + 1 < 2 ^ 63 at hσb
    iunfold chunkIs at Hch
    generalize hPL : pagesL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive'
      (limN opts.Predicate'.Limit') i = PL at hfrom
    icases Hch with ⟨#Hrev, %Hcc, %ps, Hkvs, #Hps⟩
    generalize hpg : pageKvsL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive' PL.1
      (if opts.Recursive' = true then PL.2 else 1) = pg at Hcc
    obtain ⟨hpg1, hpg2⟩ := pageKvsL_prefix (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive'
      PL.1 (if opts.Recursive' = true then PL.2 else 1)
    rw [hpg, hfrom] at hpg1 hpg2
    generalize hrest : ((scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive').drop m).drop
      pg.1.length = rest at hpg1
    ihave %Hpsl := BigSepL2.bigSepL2_length $$ Hps
    ihave %Hkl := ownSlice_len $$ Hkvs
    iapply Hy $$ %_ %_ %_ [] HTok
    · ipureintro; exact ⟨by simp, by simp⟩
    iapply wp_post_named
    iintro %Ψb %hΨb
    wp_auto
    ihave %Hrn := typedPointsto_not_null _ _ _ $$ Hrev
    rw [show decide (ch.revision' = null) = false from decide_eq_false Hrn]
    wp_auto
    have hσr : uint.nat (W64 (σ.rev : Int)) = σ.rev := by word
    have hscl : (scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive').length < 2 ^ 41 := by
      have h1 := (hks (uint.nat R) hRle).1
      have h2 : (scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive').length ≤
          (σ.at (uint.nat R)).kvs.length := List.length_filter_le _ _
      omega
    have hmp : m + pg.1.length + rest.length =
        (scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive').length := by
      have := congrArg List.length hpg1
      simp only [List.length_drop, List.length_append] at this
      omega
    have hkvl : sint.nat ch.kvs'.len = pg.1.length := by rw [← Hkl.1]; exact Hpsl
    have hfetch : W64 (m : Int) + ch.kvs'.len = W64 ((m + pg.1.length : Nat) : Int) := by
      have := Hkl.2
      word
    rw [hfetch]
    -- the revision check: `withRev` becomes `R`, or a too-large error returns
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun bv => iprop(
        (⌜bv = executeVal ∧ (uint.Z R0 = 0 → ¬ σ.rev < uint.nat n)⌝ ∗ withRev_ptr ↦ R ∗
          (∃ e' : GoInterface, err_ptr ↦ e') ∗ «$res0_ptr» ↦ GoInterface.nil ∗ chunk_ptr ↦ ch) ∨
        (⌜bv = returnVal #()⌝ ∗ (HkP -∗ numFetched_ptr ↦ W64 ((m + pg.1.length : Nat) : Int) -∗
          numEvald_ptr ↦ nev -∗ v_ptr ↦ rv -∗ L.itemsRef pl ↦ sl -∗ L.itemsAt sl (itemsOf c st) -∗
          Ψb (returnVal #())))))) $$ [withRev err «$res0» chunk]
    · by_cases hw0 : wr = W64 0
      · rw [show decide (wr = W64 0) = true from decide_eq_true hw0]
        wp_auto
        wp_apply (wp_validateMin Obj sp c opts.ResourceVersion' n R) $$ [] as %verr Hverr
        · iframe #
          ipureintro; exact hrv
        have hR0z : uint.Z R0 = 0 := by
          by_cases hi : i = 0
          · have h1 := (hi0 hi).1
            rw [hw0] at h1
            rw [← h1]; decide
          · refine Classical.byContradiction fun h => ?_
            have h2 := (hi1 hi).1
            rw [if_neg h] at hR
            rw [hw0, hR] at h2
            apply h; rw [← h2]; decide
        rw [if_pos hR0z] at hR
        by_cases hlt : uint.nat R < uint.nat n
        · rw [if_pos hlt]
          icases persistent_entails_left (apierrors.tooLargeErrIs_ptr verr) $$ Hverr with
            ⟨Hverr, %Hptr⟩
          obtain ⟨l, rfl⟩ := Hptr
          wp_auto
          iright
          isplitr
          · ipureintro; rfl
          iintro Hk numFetched numEvald v Hip Hits
          rw [hΨb]
          unfold forRangePost
          iright
          isplitr
          · ipureintro; exact Or.inr ⟨_, rfl, by simp⟩
          iintro HD
          iexists false
          isplitr
          · ipureintro; rfl
          simp only [Bool.false_eq_true, ↓reduceIte]
          iintro Htt
          isplitr
          · ipureintro; simp
          iright; iright
          iexists #()
          iframe HD
          rw [hHkP]
          icases Hk with ⟨-, Hret⟩
          iapply Hret $$ %_ %_ %_ %_ %_ «$res0» numFetched numEvald v Hip Hits Htt []
          · ipureintro; exact ⟨by word, hnev0⟩
          iright
          iexists (W64 (σ.rev : Int)), σ
          iframe HQσ Hverr
          ipureintro
          rw [if_pos hR0z]
          rw [hR, hσr] at hlt; exact hlt
        · rw [if_neg hlt]
          icases Hverr with %Hverr
          subst Hverr
          wp_auto
          ileft
          iframe
          ipureintro
          refine ⟨rfl, fun _ => ?_⟩
          rw [hR, hσr] at hlt; exact hlt
      · rw [show decide (wr = W64 0) = false from decide_eq_false hw0]
        wp_auto
        have hwR : wr = R := by
          by_cases hi : i = 0
          · obtain ⟨h1, -⟩ := hi0 hi
            subst h1
            have : ¬ uint.Z wr = 0 := by intro h; apply hw0; word
            rw [if_neg this] at hR; exact hR.symm
          · exact (hi1 hi).1
        subst hwR
        rw [show decide (wr = wr) = true from decide_eq_true rfl]
        wp_auto
        ileft
        iframe
        ipureintro
        refine ⟨rfl, fun h => ?_⟩
        by_cases hi : i = 0
        · exfalso; apply hw0; rw [(hi0 hi).1]; word
        · exact (hi1 hi).2.2 h
    iintro %bv Hbv
    icases Hbv with (⟨%Hbv, withRev, ⟨%e1, err⟩, «$res0», chunk⟩ | ⟨%Hbv, HΨ⟩)
    · obtain ⟨rfl, hRn⟩ := Hbv
      wp_auto
      have hmne : pg.1.length < pg.2 → pg.1 ≠ [] := by
        rw [← hpg]; exact pageKvsL_more_ne _ _ _ _ _
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun bv => iprop(⌜bv = executeVal⌝ ∗ chunk_ptr ↦ ch))) $$ [chunk]
      · by_cases hz : ch.kvs'.len = W64 0
        · have hp0 : pg.1 = [] := by
            rw [hz] at hkvl; exact List.eq_nil_of_length_eq_zero (by rw [← hkvl]; rfl)
          have hhm0 : ch.hasMore' = false := by
            rw [Hcc.2]; exact decide_eq_false (fun h => hmne h hp0)
          rw [show decide (ch.kvs'.len = W64 0) = true from decide_eq_true hz]
          wp_auto
          rw [hhm0]
          wp_auto
          iframe
          ipureintro; rfl
        · rw [show decide (ch.kvs'.len = W64 0) = false from decide_eq_false hz]
          wp_auto
          iframe
          ipureintro; rfl
      iintro %bv ⟨%Hbv, chunk⟩
      subst Hbv
      wp_auto
      have hpgsc : ∀ kv ∈ pg.1, kv ∈ scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive' := by
        intro kv hkv
        have : kv ∈ (scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive').drop m := by
          rw [hpg1]; exact List.mem_append_left _ hkv
        exact List.mem_of_mem_drop this
      have hdec : ∀ kv ∈ scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive',
          c.S.dec kv.value ≠ none := by
        intro kv hkv
        have hpf : c.pfx <+: kv.key :=
          (prepareKeyM_prefix c.pathPrefix c.resourcePrefix key k opts.Recursive' hk).trans
            (scopeL_prefix _ _ _ _ hkv)
        exact (hwh (uint.nat R) hRle kv (List.mem_filter.1 hkv).1).1 hpf
      have hmod : ∀ kv ∈ pg.1, 0 ≤ sint.Z kv.modRev := by
        intro kv hkv
        have h1 := (hwh (uint.nat R) hRle kv (List.mem_filter.1 (hpgsc kv hkv)).1).2
        have : uint.nat kv.modRev < 2 ^ 63 := by omega
        word
      have hpaging : decide (sint.Z (W64 0) < sint.Z opts.Predicate'.Limit') =
          decide (0 < sint.Z opts.Predicate'.Limit') := rfl
      wp_apply (wp_appendChunk Obj sp c L (GoInterface.ok ci') ch.kvs' ps pg.1 opts.Predicate' sel emp
          nf ag rv (L.itemsRef pl) _ st (fun kv h => hdec kv (hpgsc kv h)) hmod (by omega) hpaging)
        $$ [Hkvs Hip Hits] as %lk %evd %lr ⟨%Hlr, ⟨%ps', Hkvs⟩, ⟨%sl', Hip, Hits⟩, %n', %Hn', #Hlk⟩
      · iframe # Hkvs
        isplitr
        · ipureintro; exact Hrv
        isplitl
        · iexists sl; iframe
        ipureintro; exact hstm
      obtain ⟨hn'1, hn'2, hn'3, hn'4, hn'5⟩ := Hn'
      have hkpne : c.pathPrefix ++ k ≠ [] := by
        have := prepareKeyM_ne_nil _ _ _ _ hk
        intro h; exact this (List.append_eq_nil_iff.1 h).2
      -- the last key
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun bv => iprop(⌜bv = executeVal⌝ ∗ ∃ (lkp' : GoSlice) (lkb' : GoString),
          lastKey_ptr ↦ lkp' ∗ lkp' ↦*□ lkb' ∗
          ⌜0 < n' → ∃ kv, pg.1[n' - 1]? = some kv ∧ lkb' = kv.key⌝))) $$ [lastKey chunkLastKey]
      · by_cases hl : lk = slice.nil
        · rw [show decide (lk = slice.nil) = true from decide_eq_true hl]
          wp_auto
          ihave %Hn0 : ⌜n' = 0⌝ $$ []
          · unfold lastKeyIs
            by_cases h0 : n' = 0
            · ipureintro; exact h0
            · rw [if_neg h0]
              icases Hlk with ⟨%kv, %Hkv, #Hks⟩
              subst hl
              ihave %Hl := ownSlice_len _ _ _ $$ Hks
              exfalso
              have hkvm : kv ∈ pg.1 := List.mem_of_getElem? Hkv
              have hpre := scopeL_prefix _ _ _ _ (hpgsc kv hkvm)
              have h0' : kv.key = [] := List.eq_nil_of_length_eq_zero (by rw [Hl.1]; rfl)
              rw [h0'] at hpre
              exact hkpne (List.prefix_nil.1 hpre)
          isplitr
          · ipureintro; rfl
          iexists lkp, lkb
          iframe
          isplitl []
          · iexact Hlkb
          ipureintro; intro h; omega
        · rw [show decide (lk = slice.nil) = false from decide_eq_false hl]
          wp_auto
          unfold lastKeyIs
          by_cases h0 : n' = 0
          · rw [if_pos h0]
            icases Hlk with %Hl
            exact absurd Hl hl
          · rw [if_neg h0]
            icases Hlk with ⟨%kv, %Hkv, #Hks⟩
            isplitr
            · ipureintro; rfl
            iexists lk, kv.key
            iframe
            isplitl []
            · iexact Hks
            ipureintro; intro _; exact ⟨kv, Hkv, rfl⟩
      iintro %bv ⟨%Hbv, %lkp', %lkb', lastKey, #Hlkb', %Hlk'⟩
      subst Hbv
      wp_auto
      have hst' : chunkL (fun x => sel x.1) (limN opts.Predicate'.Limit') st (decodedL c.S.dec pg.1) =
          chunkL (fun x => sel x.1) (limN opts.Predicate'.Limit') ⟨[], none, false, 0⟩
            (decodedL c.S.dec ((scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k)
              opts.Recursive').take (m + pg.1.length))) := by
        rw [hst]
        exact chunkL_take_add _ _ _ _ _ _ hpg1 (decodedL c.S.dec) (decodedL_append' _) _
      have hpg2' : pg.2 = pg.1.length + rest.length := by
        rw [hpg2, hpg1, List.length_append]
      have hhmc : ch.hasMore' = decide (rest ≠ []) := by
        rw [Hcc.2, hpg2']
        apply decide_eq_decide.2
        constructor
        · intro h he; rw [he] at h; simp at h
        · intro h; have := List.length_pos_iff.2 h; omega
      generalize hst'd : chunkL (fun x => sel x.1) (limN opts.Predicate'.Limit') st
        (decodedL c.S.dec pg.1) = st' at hst' Hlr hn'4 hn'5
      icases persistent_entails_left (L.itemsAt_len _ _) $$ Hits with ⟨Hits, %Hil⟩
      icases persistent_entails_left (L.itemsAt_wf _ _) $$ Hits with ⟨Hits, %Hiw⟩
      have Hil' : uint.nat sl'.len = st'.items.length := by rw [Hil]; simp [itemsOf]
      ihave Hbrk : (∀ hmv' : Bool, ⌜hmv' = (ch.hasMore' || lr) ∧ (lr = true ∨ ch.hasMore' = false ∨
          (0 < limN opts.Predicate'.Limit' ∧ limN opts.Predicate'.Limit' ≤ st'.items.length))⌝ -∗
          hasMore_ptr ↦ hmv' -∗ v_ptr ↦ rv -∗ L.itemsRef pl ↦ sl' -∗ Ψb breakVal) ∧
          (HkP ∗ «$res0_ptr» ↦ GoInterface.nil ∗ withRev_ptr ↦ R ∗ lastKey_ptr ↦ lkp' ∗
            count_ptr ↦ ch.count' ∗ numFetched_ptr ↦ W64 ((m + pg.1.length : Nat) : Int) ∗
            numEvald_ptr ↦ (nev + evd) ∗ err_ptr ↦ e1 ∗ L.itemsAt sl' (itemsOf c st')) $$
          [Hk «$res0» withRev lastKey count numFetched numEvald err Hits]
      · isplit
        · iintro %hmv' %Hh hasMore v Hip
          obtain ⟨hhmv, hcase⟩ := Hh
          have hcase' : st'.more = true ∨ rest = [] ∨ (0 < limN opts.Predicate'.Limit' ∧
              limN opts.Predicate'.Limit' ≤ st'.items.length) := by
            rcases hcase with h | h | h
            · left; rw [← Hlr]; exact h
            · right; left
              rw [hhmc] at h
              exact Decidable.of_not_not (fun hn => by simp [hn] at h)
            · right; right; exact h
          obtain ⟨ha1, ha2, ha3⟩ := kListL_final c.S.dec sel (limN opts.Predicate'.Limit')
            (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive' m pg.1 rest hpg1 hdec st' hst' hcase'
          have hmvA : hmv' = (kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k)
              opts.Recursive' (σ.at (uint.nat R))).more := by
            rw [ha3, hhmv, hhmc, Hlr]
            cases st'.more <;> simp
          have hn'pos : hmv' = true → 0 < n' := by
            intro hm
            refine Nat.pos_of_ne_zero fun h0 => ?_
            cases hlr : lr
            · rw [hhmv, hlr, Bool.or_false, hhmc] at hm
              have hr : rest ≠ [] := of_decide_eq_true hm
              have hn0 := hn'3 hlr
              rw [h0] at hn0
              have hne := hmne (by rw [hpg2']; have := List.length_pos_iff.2 hr; omega)
              exact hne (List.eq_nil_of_length_eq_zero hn0.symm)
            · exact hstf (hn'4 hlr h0)
          rw [hΨb]
          unfold forRangePost
          iright
          isplitr
          · ipureintro; exact Or.inl rfl
          iintro HD
          iexists false
          isplitr
          · ipureintro; rfl
          simp only [Bool.false_eq_true, ↓reduceIte]
          iintro Htt
          isplitr
          · ipureintro; simp
          iright; ileft
          iframe HD
          rw [hHkP]
          icases Hk with ⟨Hfin, -⟩
          iapply Hfin $$ %σ %R %R %lkp' %lkb' %hmv' %ch.count' %(W64 ((m + pg.1.length : Nat) : Int))
            %(nev + evd) %e1 %sl' %st' «$res0» withRev lastKey Hlkb' hasMore count numFetched numEvald err
            v Hip Hits HQσ Htt []
          ipureintro
          refine ⟨hR, hRle, hσb, hRn, rfl, ha1.symm, hmvA, ?_, ?_, by word, ?_⟩
          · intro hm
            have hn := hn'pos hm
            have hor : lr = true ∨ 0 < limN opts.Predicate'.Limit' ∧
                limN opts.Predicate'.Limit' ≤ st'.items.length := by
              rcases hcase with h | h | h
              · exact Or.inl h
              · cases hlr : lr
                · exfalso
                  rw [hhmv, h, hlr] at hm; cases hm
                · exact Or.inl rfl
              · exact Or.inr h
            obtain ⟨kv, hkv, hlast⟩ := hn'5 hn hor
            obtain ⟨kv', hkv', hlkb⟩ := Hlk' hn
            rw [hkv] at hkv'
            cases hkv'
            refine ⟨by rw [ha2, hlast, hlkb], ?_⟩
            rw [hlkb]
            exact scopeL_prefix _ _ _ _ (hpgsc kv (List.mem_of_getElem? hkv))
          · intro hm he
            have hi : i = 0 := by
              refine Classical.byContradiction fun hi => ?_
              rw [(hi1 hi).2.1] at he; cases he
            obtain ⟨-, hm0⟩ := hi0 hi
            subst hm0
            rw [Hcc.1, kListL_total _ _ _ _ _ _ hdec, hpg2]
            simp
          · rw [hn'2]
            have := hn'1
            word
        · iframe
      cases hlr : lr
      · cases hhm : ch.hasMore'
        · -- nothing is left: `break`
          wp_auto
          rw [hhm]
          wp_auto
          icases Hbrk with ⟨Hbrk, -⟩
          iapply Hbrk $$ %false [] hasMore v Hip
          ipureintro; exact ⟨rfl, Or.inr (Or.inl rfl)⟩
        · wp_auto
          rw [hhm]
          wp_auto
          wp_bind (If _ _ _)
          iapply (wp_wand (Φ := fun bv => iprop(
              (⌜bv = executeVal ∧ ¬ (0 < limN opts.Predicate'.Limit' ∧
                limN opts.Predicate'.Limit' ≤ st'.items.length)⌝ ∗ v_ptr ↦ rv ∗ L.itemsRef pl ↦ sl' ∗
                hasMore_ptr ↦ true ∗
                (HkP ∗ «$res0_ptr» ↦ GoInterface.nil ∗ withRev_ptr ↦ R ∗ lastKey_ptr ↦ lkp' ∗
                  count_ptr ↦ ch.count' ∗ numFetched_ptr ↦ W64 ((m + pg.1.length : Nat) : Int) ∗
                  numEvald_ptr ↦ (nev + evd) ∗ err_ptr ↦ e1 ∗ L.itemsAt sl' (itemsOf c st'))) ∨
              (⌜bv = breakVal⌝ ∗ Ψb breakVal)))) $$ [v Hip hasMore Hbrk]
          · by_cases hp : 0 < sint.Z opts.Predicate'.Limit'
            · rw [show decide (sint.Z (W64 0) < sint.Z opts.Predicate'.Limit') = true from
                decide_eq_true hp]
              wp_auto
              wp_apply (wp_Len v_ptr _ _ rv c.S.objTy (L.itemsRef pl) sl') $$ [$v $Hip] as ⟨v, Hip⟩
              · iframe #
                ipureintro; exact Hrv
              (try wp_auto)
              have hlimn : limN opts.Predicate'.Limit' = sint.nat opts.Predicate'.Limit' := by
                unfold limN; rw [if_pos hp]
              by_cases hge : sint.Z opts.Predicate'.Limit' ≤ sint.Z sl'.len
              · rw [show decide (sint.Z opts.Predicate'.Limit' ≤ sint.Z sl'.len) = true from
                  decide_eq_true hge]
                wp_auto
                iright
                isplitr
                · ipureintro; rfl
                icases Hbrk with ⟨Hbrk, -⟩
                iapply Hbrk $$ %true [] hasMore v Hip
                ipureintro
                refine ⟨by simp, Or.inr (Or.inr ⟨by rw [hlimn]; word, ?_⟩)⟩
                rw [hlimn, ← Hil']
                have := Hiw.1
                word
              · rw [show decide (sint.Z opts.Predicate'.Limit' ≤ sint.Z sl'.len) = false from
                  decide_eq_false hge]
                wp_auto
                icases Hbrk with ⟨-, Hrest⟩
                ileft
                iframe
                ipureintro
                refine ⟨rfl, fun h => ?_⟩
                have h2 := h.2
                rw [hlimn, ← Hil'] at h2
                have := Hiw.1
                apply hge
                word
            · rw [show decide (sint.Z (W64 0) < sint.Z opts.Predicate'.Limit') = false from
                decide_eq_false hp]
              wp_auto
              icases Hbrk with ⟨-, Hrest⟩
              ileft
              iframe
              ipureintro
              refine ⟨rfl, fun h => ?_⟩
              have := h.1
              unfold limN at this
              rw [if_neg hp] at this
              omega
          iintro %bv Hbv
          icases Hbv with (⟨%Hbv, v, Hip, hasMore, Hrest⟩ | ⟨%Hbv, HΨ⟩)
          · obtain ⟨rfl, hnf⟩ := Hbv
            (try wp_auto)
            have hmore : pg.1.length < pg.2 := of_decide_eq_true (Hcc.2 ▸ hhm)
            have hne : pg.1 ≠ [] := hmne hmore
            have hFl : ((scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive').drop m).length =
                pg.1.length + rest.length := by rw [hpg1, List.length_append]
            have hfrom' : fromL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive'
                (pagesL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive'
                  (limN opts.Predicate'.Limit') (i + 1)).1 =
                (scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive').drop
                  (m + pg.1.length) := by
              rw [pagesL, hPL]
              simp only []
              rw [hpg]
              have hl0 : 0 < pg.1.length := List.length_pos_iff.2 hne
              have hlast : pg.1.getLast? = some ((fromL (σ.at (uint.nat R)) (c.pathPrefix ++ k)
                  opts.Recursive' PL.1)[pg.1.length - 1]'(by rw [hfrom, hFl]; omega)) := by
                rw [List.getLast?_eq_getElem?]
                simp only [hfrom, hpg1]
                rw [List.getElem_append_left (by omega)]
                exact List.getElem?_eq_getElem _
              rw [hlast]
              simp only [Option.map_some, Option.getD_some]
              rw [fromL_next _ _ _ _ _ hl0 (by rw [hfrom, hFl]; omega), hfrom, List.drop_drop]
            have hpm : pageMore (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive'
                (limN opts.Predicate'.Limit') (i + 1 - 1) = true := by
              simp only [Nat.add_sub_cancel, pageMore, hPL, hpg]
              exact decide_eq_true hmore
            have hstm' : st'.more = false := by
              first | exact Hlr.symm | (rw [← Hlr]; exact hlr)
            ihave %Hselp : ⌜emp = true → ∀ o, sel o = true⌝ $$ []
            · iunfold selPredOk at Hsel
              icases Hsel with ⟨%Hs, -⟩
              ipureintro; exact Hs.2
            have hemp : emp = false := by
              by_cases hi : i = 0
              · obtain ⟨-, hm0⟩ := hi0 hi
                subst hm0
                cases hemp : emp
                · rfl
                · exfalso
                  subst hi
                  have hst0 : st = ⟨[], none, false, 0⟩ := by rw [hst]; rfl
                  rw [hst0] at hst'd
                  have hPL0 : PL = (c.pathPrefix ++ k, limN opts.Predicate'.Limit') := by
                    rw [← hPL]; rfl
                  subst hPL0
                  cases hrec : opts.Recursive'
                  · rw [hrec] at hpg
                    simp only [Bool.false_eq_true, ↓reduceIte] at hpg
                    rw [pageKvsL_key] at hpg
                    rw [← hpg] at hmore
                    exact Nat.lt_irrefl _ hmore
                  · rw [hrec] at hpg hfrom hpg2 hdec
                    simp only [↓reduceIte] at hpg
                    have hpg1' := congrArg Prod.fst hpg
                    rw [pageKvsL_eq, hfrom] at hpg1'
                    have hdec' : ∀ kv ∈ (scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) true).drop 0,
                        c.S.dec kv.value ≠ none := fun kv h => hdec kv (List.mem_of_mem_drop h)
                    have hmore' : pg.1.length <
                        ((scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) true).drop 0).length := by
                      rw [← hpg2]; exact hmore
                    have hfull := page0_full c.S.dec sel (Hselp hemp) (limN opts.Predicate'.Limit')
                      _ pg.1 hdec' hpg1'.symm hmore'
                    rw [hst'd] at hfull
                    exact hnf hfull
              · exact (hi1 hi).2.1
            rw [hΨb]
            unfold forRangePost
            ileft
            isplitr
            · ipureintro; exact Or.inl rfl
            iintro HTok'
            iexists true
            isplitr
            · ipureintro; rfl
            simp only [↓reduceIte]
            icases Hrest with ⟨Hk, «$res0», withRev, lastKey, count, numFetched, numEvald, err, Hits⟩
            iexists R, lkp', lkb', true, ch.count', nev + evd, m + pg.1.length, e1, GoInterface.nil,
              ch, sl', st'
            iframe
            isplitl []
            · iexact Hlkb'
            iframe HQσ
            ipureintro
            refine ⟨by omega, rfl, ⟨hR, hRle, hσb, hRn, hfrom', by omega, hst', hstm', hnf, ?_, ?_⟩,
              hemp, hpm⟩
            · rw [hn'2]; word
            · rw [hn'2]; word
          · subst Hbv
            (try wp_auto)
            iexact HΨ
      · -- the limit was reached: `break`
        (try wp_auto)
        cases hhm : ch.hasMore' <;> wp_auto <;>
        · icases Hbrk with ⟨Hbrk, -⟩
          iapply Hbrk $$ %true [] hasMore v Hip
          ipureintro; exact ⟨by simp [hhm], Or.inl rfl⟩
    · subst Hbv
      wp_auto
      iapply HΨ $$ Hk numFetched numEvald v Hip Hits
  · -- an error
    iintro !> %o %i %e HJ Herr
    simp only
    icases HJ with ⟨%wr, %lkp, %lkb, %hmv, %cnt, %nev, %m, %e0, %chE, %chv, %sl, %st, HTok, Hk,
      «$res0», withRev, lastKey, #Hlkb, hasMore, count, numFetched, numEvald, err, chunk, chunkErr, v,
      Hip, Hits, Ho⟩
    ihave %Hene : ⌜e ≠ GoInterface.nil⌝ $$ [Herr]
    · icases Herr with (⟨#Htl, -⟩ | #Hle)
      · ihave %Hp := apierrors.tooLargeErrIs_ptr e $$ Htl
        obtain ⟨l, rfl⟩ := Hp
        ipureintro; nofun
      · iunfold listErr at Hle
        icases Hle with (#Hu | ⟨%st', #Ha, -⟩)
        · iapply unkErr_ne c e $$ Hu
        · iunfold apierrors.apiErrAt at Ha
          icases Ha with ⟨%l, %Hl, -⟩
          ipureintro; rw [Hl]; nofun
    ihave %Hnn : ⌜0 ≤ sint.Z (W64 (m : Int)) ∧ 0 ≤ sint.Z nev⌝ $$ [Ho]
    · cases o with
      | none =>
        simp only
        icases Ho with %Ho
        obtain ⟨-, -, rfl, -, rfl⟩ := Ho
        ipureintro; exact ⟨by decide, by decide⟩
      | some x =>
        obtain ⟨σ, R⟩ := x
        simp only
        icases Ho with ⟨#HQσ, %Ho⟩
        obtain ⟨-, -, Hpg, -, -⟩ := Ho
        obtain ⟨-, hRle, -, -, -, hm, -, -, -, hnev, -⟩ := Hpg
        ihave %Hwf := (hQ _ σ) $$ HQσ
        have hsc : (scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive').length <
            2 ^ 41 := by
          have h1 := (Hwf.2.2 (uint.nat R) hRle).1
          have h2 : (scopeL (σ.at (uint.nat R)) (c.pathPrefix ++ k) opts.Recursive').length ≤
              (σ.at (uint.nat R)).kvs.length := List.length_filter_le _ _
          omega
        ipureintro
        exact ⟨by word, hnev⟩
    obtain ⟨ei, rfl⟩ : ∃ ei, e = GoInterface.ok ei := by
      cases e with
      | nil => exact absurd rfl Hene
      | ok ei => exact ⟨ei, rfl⟩
    iapply Hy $$ %_ %_ %_ [] HTok
    · ipureintro; exact ⟨by simp, by simp⟩
    wp_auto
    unfold forRangePost
    iright
    isplitr
    · ipureintro; exact Or.inr ⟨_, rfl, by simp⟩
    iintro HD
    iexists false
    isplitr
    · ipureintro; rfl
    iintro Htt
    isplitr
    · ipureintro; simp
    iright; iright
    iexists #()
    iframe HD
    rw [hHkP]
    icases Hk with ⟨-, Hret⟩
    iapply Hret $$ %_ %_ %_ %_ %_ «$res0» numFetched numEvald v Hip Hits Htt %Hnn
    icases Herr with (⟨#Htl, %Ho0, %R', %σ, #HQσ, %Hlt⟩ | #Hle)
    · iright
      iexists R', σ
      iframe HQσ Htl
      ipureintro
      have h0 : ¬ uint.Z R0 = 0 := by
        intro h
        have : uint.nat R0 = 0 := by word
        omega
      rw [if_neg h0]; exact Hlt
    · ileft; iexact Hle
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
