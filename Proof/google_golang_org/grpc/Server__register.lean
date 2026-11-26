/-
Proof of `Spec/google_golang_org/grpc/Server__register.lean` over the model's body (W1, 2026-11-26):
under `mu`, no event log (`printf` does nothing), not serving, the service name new (`services` has no
entry for it); the `serviceInfo` with its `streams` map built in `register`'s order, each stream's
descriptor `&sd.Streams[i]`, then each method's fresh `StreamDesc` over `wrapUnaryHandler(&sd.Methods[j])`
(the names are distinct, so the map is `srvStreamsL`'s); then `services[sd.ServiceName] = info`.
-/
module

public import Spec.google_golang_org.grpc.Server__register
public import Spec.google_golang_org.grpc.Server__printf
public import Spec.google_golang_org.grpc.Server__wrapUnaryHandler

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section pure
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

theorem grpcReg_lookupL_snoc {K V : Type} [DecidableEq K] (n k : K) (v : V) :
    ∀ (l : List (K × V)), k ∉ l.map Prod.fst →
      map.lookupL n (l ++ [(k, v)]) = if k = n then some v else map.lookupL n l
  | [], _ => by
    by_cases h : k = n
    · subst h; simp [map.lookupL]
    · simp [map.lookupL, h, Ne.symm h]
  | p :: ps, hk => by
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    simp only [List.cons_append, map.lookupL]
    by_cases h : n = p.1
    · have hkn : ¬ k = n := by rw [h]; exact hk.1
      rw [if_pos h, if_neg hkn, if_pos h]
    · rw [if_neg h, if_neg h, grpcReg_lookupL_snoc n k v ps hk.2]

theorem grpcReg_nodup_not_mem_take {α : Type} :
    ∀ (l : List α) (k : Nat) (x : α), l.Nodup → l[k]? = some x → x ∉ l.take k
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _ => by simp
  | y :: l, k + 1, x, hnd, h => by
    rw [List.nodup_cons] at hnd
    simp only [List.getElem?_cons_succ] at h
    simp only [List.take_succ_cons, List.mem_cons, not_or]
    exact ⟨fun hxy => hnd.1 (hxy ▸ List.mem_of_getElem? h),
      grpcReg_nodup_not_mem_take l k x hnd.2 h⟩

theorem grpcReg_zip_snoc_right {α β : Type} :
    ∀ (l : List α) (r : List β) (a : α) (b : β),
      l[r.length]? = some a → l.zip (r ++ [b]) = l.zip r ++ [(a, b)]
  | [], _, _, _, h => by simp at h
  | x :: xs, [], a, b, h => by
    simp only [List.length_nil, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp
  | x :: xs, c :: r, a, b, h => by
    simp only [List.length_cons, List.getElem?_cons_succ] at h
    simp only [List.cons_append, List.zip_cons_cons, grpcReg_zip_snoc_right xs r a b h]

theorem grpcReg_zipIdx_map_fst {α β γ : Type} (f : α → β) (g : Nat → γ) :
    ∀ (l : List α) (n : Nat), ((l.zipIdx n).map fun (a, i) => (f a, g i)).map Prod.fst = l.map f
  | [], _ => rfl
  | a :: l, n => by
    simp only [List.zipIdx_cons, List.map_cons, grpcReg_zipIdx_map_fst f g l (n + 1)]

theorem grpcReg_zip_map_fst {α β γ : Type} (f : α → γ) :
    ∀ (l : List α) (r : List β),
      ((l.zip r).map fun (a, b) => (f a, b)).map Prod.fst = (l.take r.length).map f
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: r => by
    simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.take_succ_cons]
    rw [grpcReg_zip_map_fst f l r]

/-- The streams' half of `srvStreamsL` (its text). -/
def grpcReg_streamsPart (sds : List google_golang_org.grpc.StreamDesc) (ssl : GoSlice) :
    List (GoString × Loc) :=
  sds.zipIdx.map fun (d, i) =>
    (d.StreamName', sliceIndexRef google_golang_org.grpc.StreamDesc (i : Int) ssl)

/-- The methods' half of `srvStreamsL` (its text). -/
def grpcReg_methodsPart (mds : List google_golang_org.grpc.MethodDesc) (mls : List Loc) :
    List (GoString × Loc) :=
  (mds.zip mls).map fun (d, l) => (d.MethodName', l)

theorem grpcReg_srvStreamsL (r : GrpcSrvReg) (ssl : GoSlice) (mls : List Loc) :
    srvStreamsL r ssl mls = grpcReg_streamsPart r.sds ssl ++ grpcReg_methodsPart r.mds mls := by
  unfold srvStreamsL grpcReg_streamsPart grpcReg_methodsPart
  rfl

theorem grpcReg_streamsPart_fst (sds : List google_golang_org.grpc.StreamDesc) (ssl : GoSlice) :
    (grpcReg_streamsPart sds ssl).map Prod.fst = sds.map (·.StreamName') :=
  grpcReg_zipIdx_map_fst (·.StreamName')
    (fun i : Nat => sliceIndexRef google_golang_org.grpc.StreamDesc (i : Int) ssl) sds 0

theorem grpcReg_methodsPart_fst (mds : List google_golang_org.grpc.MethodDesc) (mls : List Loc) :
    (grpcReg_methodsPart mds mls).map Prod.fst = (mds.take mls.length).map (·.MethodName') :=
  grpcReg_zip_map_fst (·.MethodName') mds mls

theorem grpcReg_streamsPart_take_succ (sds : List google_golang_org.grpc.StreamDesc)
    (ssl : GoSlice) (k : Nat) (d : google_golang_org.grpc.StreamDesc) (h : sds[k]? = some d) :
    (grpcReg_streamsPart sds ssl).take (k + 1) = (grpcReg_streamsPart sds ssl).take k ++
      [(d.StreamName', sliceIndexRef google_golang_org.grpc.StreamDesc (k : Int) ssl)] := by
  rw [List.take_add_one]
  congr 1
  unfold grpcReg_streamsPart
  rw [List.getElem?_map, List.getElem?_zipIdx, h]
  simp

theorem grpcReg_methodsPart_snoc (mds : List google_golang_org.grpc.MethodDesc) (mls : List Loc)
    (d : google_golang_org.grpc.MethodDesc) (ml : Loc) (h : mds[mls.length]? = some d) :
    grpcReg_methodsPart mds (mls ++ [ml]) = grpcReg_methodsPart mds mls ++ [(d.MethodName', ml)] := by
  unfold grpcReg_methodsPart
  rw [grpcReg_zip_snoc_right mds mls d ml h]
  simp

theorem grpcReg_zip_snoc {α β : Type} (l : List α) (r : List β) (a : α) (b : β)
    (h : l.length = r.length) : (l ++ [a]).zip (r ++ [b]) = l.zip r ++ [(a, b)] := by
  rw [List.zip_append h]
  rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.Assumptions]

/-- A condition variable's fact carries `sync`'s package fact (what `Mutex.Lock` takes). -/
theorem grpcReg_isCond_pkg (c : Loc) (m : GoInterfaceOk) :
    sync.isCond (GF := GF) c m ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync := by
  rw [sync.isCond_unseal]
  unfold sync.isCondDef
  iintro H
  iNamed H
  iexact Hi

set_option maxHeartbeats 4000000 in
theorem grpc.Server.register.wp_proof
    (wp_printf : grpc.Server.printf.spec (GF := GF) (hG := hG))
    (wp_wrapUnaryHandler : grpc.Server.wrapUnaryHandler.spec (GF := GF) (hG := hG)) :
    grpc.Server.register.spec (GF := GF) (hG := hG) := by
  intro gs sd ss ics sics svcs regs sregs sn ht mds sds
  wp_start as ⟨Hsrv, #Hdesc, %Hsn, %Himpl, %Hnd, %Hst⟩
  ihave #Hdcopy : (grpcDescIs (GF := GF) sd sn ht mds sds) $$ []
  · iexact Hdesc
  iunfold grpcSrvNew at Hsrv
  icases Hsrv with ⟨%so, %sh, %lis, %conns, %svm, %cv, %q, %dn, %rs, %ils, %M, Hopts, Hsoi, Hsh,
    #Hmu, Hlis, Hlism, Hconns, Hconnsm, Hserve, Hdrain, Hcvp, #Hcond, Hsvc, Hsvm, Hev, Hquit, Hq,
    Hdone, Hdn, Hswg, Hhwg, %Hinv, Hregs⟩
  obtain ⟨Hsvcs, Hsvnd, Hils, HM, Hregs', Hsregs', Hflag⟩ := Hinv
  iunfold grpcDescIs at Hdesc
  icases Hdesc with ⟨%msl, %ssl, #Hsn', #Hht, #Hmsl, #Hmds, #Hssl, #Hsds, %mdv, #Hmdv⟩
  ihave %Hmdl := ownSlice_len _ _ _ $$ Hmds
  ihave %Hsdl := ownSlice_len _ _ _ $$ Hsds
  ihave #Hsync := grpcReg_isCond_pkg _ _ $$ Hcond
  have Hnd' := Hnd
  unfold descNames at Hnd'
  obtain ⟨HndM, HndS, HndMS⟩ := List.nodup_append.1 Hnd'
  have Hlen : svcs.length = ils.length := by rw [Hsvcs, List.length_map, Hils]
  have hMsn : M !! sn = none := by
    rw [HM sn]
    exact (map.lookupL_eq_none_iff _ _).2
      (by rw [List.map_fst_zip (l₁ := svcs) (l₂ := ils) (by omega)]; exact Hsn)
  (try wp_auto)
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, -⟩
  (try wp_auto)
  -- `s.printf("RegisterService(%q)", sd.ServiceName)`: no event log
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any) [_]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %asl -
  (try wp_auto)
  wp_apply (wp_printf gs _ _) $$ [$Hev] as Hev
  -- not serving; `s.services[sd.ServiceName]`: no entry
  wp_apply (wp_map_lookup2 (K := GoString) (V := Loc) go.string
    (go.GoType.PointerType google_golang_org.grpc.serviceInfo.ty) svm M sn (DFrac.own 1))
    $$ [$Hsvm] as Hsvm
  wp_if_destruct
  · exfalso
    simp [hMsn] at Hif
  -- `info := &serviceInfo{ss, make(map[string]*StreamDesc), sd.Metadata}`
  wp_apply (wp_map_make1 (K := GoString) (V := Loc)) as %stm Hstm
  (try wp_auto)
  -- `for i := range sd.Streams`
  irename «$r0» => Hinfo
  generalize «$r0_ptr» = il at *
  rename_i ireg
  irename i => Hcnt
  irename i => Hireg
  ihave IH : iprop(∃ (n : w64) (iv : w64) (M2 : GMap GoString Loc),
      "Hcnt" ∷ i_ptr ↦ n ∗ "Hireg" ∷ ireg ↦ iv ∗ "Hstm" ∷ stm ↦$ M2 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ sds.length ∧
        ∀ x : GoString, M2 !! x = map.lookupL x ((grpcReg_streamsPart sds ssl).take (sint.nat n))⌝)
    $$ [Hcnt Hireg Hstm]
  · iexists W64 0, _, ∅
    simp only [named]
    iframe
    ipureintro
    refine ⟨by decide, by word, fun x => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    rfl
  wp_for IH
  wp_if_destruct
  · -- an iteration: `info.streams[sd.Streams[i].StreamName] = &sd.Streams[i]`
    obtain ⟨Hn0, Hnle, HM2⟩ := Hn
    have Hif : sint.Z n < sint.Z ssl.len
      := by first | exact Hif | (have := go.intoVal_inj Hif; simpa using this)
    have Hk : sint.nat n < sds.length := by rw [Hsdl.1]; word
    obtain ⟨dv, Hdv⟩ : ∃ dv, sds[sint.nat n]? = some dv := ⟨_, List.getElem?_eq_getElem Hk⟩
    icases ownSlice_elem_acc (sint.Z n) dv ssl DFrac.discard sds Hn0 Hdv $$ Hsds with ⟨#Hel, -⟩
    iStructNamed Hel
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ssl.len := ⟨Hn0, Hif⟩
    (try simp only [Hbnd, _root_.and_self, ite_true])
    wp_apply (wp_load_slice_index ssl (sint.Z n) sds DFrac.discard dv Hn0) $$ [$Hsds] as -
    · ipureintro; exact Hdv
    (try simp only [Hbnd, _root_.and_self, ite_true])
    (try wp_auto)
    wp_apply (wp_mapInsert go.string stm M2 dv.StreamName'
      (sliceIndexRef google_golang_org.grpc.StreamDesc (sint.Z n) ssl)) $$ [$Hstm] as Hstm
    wp_for_post
    iframe
    iexists n + W64 1, n, _
    simp only [named]
    iframe
    ipureintro
    have hfresh : dv.StreamName' ∉
        ((grpcReg_streamsPart sds ssl).take (sint.nat n)).map Prod.fst := by
      rw [List.map_take, grpcReg_streamsPart_fst]
      exact grpcReg_nodup_not_mem_take _ _ _ HndS (by rw [List.getElem?_map, Hdv]; rfl)
    refine ⟨by word, by word, fun x => ?_⟩
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word,
      grpcReg_streamsPart_take_succ sds ssl (sint.nat n) dv Hdv,
      grpcReg_lookupL_snoc _ _ _ _ hfresh, GMap.lookup_insert_eq_iff, HM2 x,
      Int.toNat_of_nonneg Hn0]
  -- every stream entered: the streams' half of `srvStreamsL`
  obtain ⟨Hn0, Hnle, HM2⟩ := Hn
  have Hif : ¬ sint.Z n < sint.Z ssl.len
      := by first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h]) | (intro h; apply Hif; simp [h])
  have Hsn2 : sint.nat n = sds.length := by rw [Hsdl.1] at Hnle ⊢; word
  have HM2' : ∀ x : GoString, M2 !! x = map.lookupL x (grpcReg_streamsPart sds ssl) := by
    intro x
    rw [HM2 x, Hsn2, List.take_of_length_le]
    simp [grpcReg_streamsPart]
  -- `for i := range sd.Methods`
  rename_i ireg2
  irename i => Hcnt2
  irename i => Hireg2
  ihave IH2 : iprop(∃ (n : w64) (iv : w64) (M3 : GMap GoString Loc) (mls : List Loc),
      "Hcnt2" ∷ i_ptr ↦ n ∗ "Hireg2" ∷ ireg2 ↦ iv ∗ "Hstm" ∷ stm ↦$ M3 ∗
      "Hmls" ∷ ([∗list] j ↦ ml ∈ mls, ∃ (d : google_golang_org.grpc.MethodDesc) (cs cm : Loc),
        ⌜mds[j]? = some d⌝ ∗ cs ↦□ gs ∗
        cm ↦□ sliceIndexRef google_golang_org.grpc.MethodDesc (j : Int) msl ∗
        ml ↦□ google_golang_org.grpc.StreamDesc.mk d.MethodName' (wrapUnaryClosure cs cm) false false) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ mds.length ∧ mls.length = sint.nat n ∧
        ∀ x : GoString, M3 !! x = map.lookupL x (grpcReg_streamsPart sds ssl ++ grpcReg_methodsPart mds mls)⌝)
    $$ [Hcnt2 Hireg2 Hstm]
  · iexists W64 0, _, M2, []
    simp only [named]
    iframe
    isplitl []
    · iapply (BigSepL.bigSepL_nil_intro (P := iprop(True)))
      itrivial
    ipureintro
    refine ⟨by decide, by word, by first | rfl | word | simp, fun x => ?_⟩
    rw [HM2' x, grpcReg_methodsPart, List.zip_nil_right, List.map_nil, List.append_nil]
  wp_for IH2
  wp_if_destruct
  · -- an iteration: `info.streams[d.MethodName] = &StreamDesc{d.MethodName, s.wrapUnaryHandler(d), ...}`
    obtain ⟨Hn0, Hnle, Hmlen, HM3⟩ := Hn
    have Hif : sint.Z n < sint.Z msl.len
      := by first | exact Hif | (have := go.intoVal_inj Hif; simpa using this)
    have Hk : sint.nat n < mds.length := by rw [Hmdl.1]; word
    obtain ⟨dv, Hdv⟩ : ∃ dv, mds[sint.nat n]? = some dv := ⟨_, List.getElem?_eq_getElem Hk⟩
    icases ownSlice_elem_acc (sint.Z n) dv msl DFrac.discard mds Hn0 Hdv $$ Hmds with ⟨#Hel, -⟩
    iStructNamed Hel
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len := ⟨Hn0, Hif⟩
    (try simp only [Hbnd, _root_.and_self, ite_true])
    wp_apply (wp_load_slice_index msl (sint.Z n) mds DFrac.discard dv Hn0) $$ [$Hmds] as -
    · ipureintro; exact Hdv
    (try simp only [Hbnd, _root_.and_self, ite_true])
    (try wp_auto)
    wp_apply (wp_wrapUnaryHandler gs (sliceIndexRef google_golang_org.grpc.MethodDesc (sint.Z n) msl))
      as %cs %cm ⟨#Hcs, #Hcm⟩
    ipersist «$r0»
    wp_apply (wp_mapInsert go.string stm M3 dv.MethodName' «$r0_ptr») $$ [$Hstm] as Hstm
    wp_for_post
    iframe
    iexists n + W64 1, n, _, mls ++ [«$r0_ptr»]
    simp only [named]
    have hj : ((mls.length : Nat) : Int) = sint.Z n := by
      rw [Hmlen]; exact Int.toNat_of_nonneg Hn0
    have hdj : mds[mls.length]? = some dv := by rw [Hmlen]; exact Hdv
    -- (`iframe` splits the big separating conjunction over `mls ++ [_]` and frames `Hmls`)
    iframe
    isplitl []
    · iapply BigSepL.bigSepL_singleton.2
      simp only [Nat.zero_add]
      iexists dv, cs, cm
      rw [hj]
      isplitr
      · ipureintro; exact hdj
      isplitr
      · iexact Hcs
      isplitr
      · iexact Hcm
      iexact «$r0»
    iframe
    ipureintro
    have hfresh : dv.MethodName' ∉
        (grpcReg_streamsPart sds ssl ++ grpcReg_methodsPart mds mls).map Prod.fst := by
      rw [List.map_append, grpcReg_streamsPart_fst, grpcReg_methodsPart_fst, List.mem_append,
        not_or]
      refine ⟨fun h => HndMS _ (List.mem_map_of_mem (List.mem_of_getElem? Hdv)) _ h rfl, ?_⟩
      rw [List.map_take, Hmlen]
      exact grpcReg_nodup_not_mem_take _ _ _ HndM (by rw [List.getElem?_map, Hdv]; rfl)
    refine ⟨by word, by word,
      by rw [List.length_append, Hmlen, List.length_singleton]; word, fun x => ?_⟩
    rw [grpcReg_methodsPart_snoc mds mls dv «$r0_ptr» hdj, ← List.append_assoc,
      grpcReg_lookupL_snoc _ _ _ _ hfresh, GMap.lookup_insert_eq_iff, HM3 x]
  -- every method entered; `s.services[sd.ServiceName] = info`, then the deferred `Unlock`
  obtain ⟨Hn0, Hnle, Hmlen, HM3⟩ := Hn
  have Hif : ¬ sint.Z n < sint.Z msl.len
      := by first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h]) | (intro h; apply Hif; simp [h])
  have Hmn : mls.length = mds.length := by rw [Hmlen]; rw [Hmdl.1] at Hnle ⊢; word
  wp_apply (wp_mapInsert go.string svm M sn il) $$ [$Hsvm] as Hsvm
  wp_apply (sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF)) $$ [$Hmu $Hlk]
  · (try inext)
    itrivial
  iapply HΦ
  unfold grpcSrvNew
  iexists so, sh, lis, conns, svm, cv, q, dn,
    rs ++ [({ sd := sd, sn := sn, ht := ht, mds := mds, sds := sds, ss := ss } : GrpcSrvReg)],
    ils ++ [il], <[sn := il]> M
  isplitl [Hopts]
  · iexact Hopts
  isplitl [Hsoi]
  · iexact Hsoi
  isplitl [Hsh]
  · iexact Hsh
  isplitr
  · iexact Hmu
  isplitl [Hlis]
  · iexact Hlis
  isplitl [Hlism]
  · iexact Hlism
  isplitl [Hconns]
  · iexact Hconns
  isplitl [Hconnsm]
  · iexact Hconnsm
  isplitl [Hserve]
  · iexact Hserve
  isplitl [Hdrain]
  · iexact Hdrain
  isplitl [Hcvp]
  · iexact Hcvp
  isplitr
  · iexact Hcond
  isplitl [Hsvc]
  · iexact Hsvc
  isplitl [Hsvm]
  · iexact Hsvm
  isplitl [Hev]
  · iexact Hev
  isplitl [Hquit]
  · iexact Hquit
  isplitl [Hq]
  · iexact Hq
  isplitl [Hdone]
  · iexact Hdone
  isplitl [Hdn]
  · iexact Hdn
  isplitl [Hswg]
  · iexact Hswg
  isplitl [Hhwg]
  · iexact Hhwg
  isplitl []
  · ipureintro
    have hfr : sn ∉ (svcs.zip ils).map Prod.fst := by
      rw [List.map_fst_zip (l₁ := svcs) (l₂ := ils) (by omega)]; exact Hsn
    refine ⟨by rw [List.map_append, ← Hsvcs], ?_, by simp [Hils], fun x => ?_, ?_, ?_, ?_⟩
    · refine List.nodup_append.2 ⟨Hsvnd, List.nodup_singleton sn, fun a ha b hb hab => ?_⟩
      rw [List.mem_singleton] at hb
      rw [hab, hb] at ha
      exact Hsn ha
    · rw [grpcReg_zip_snoc _ _ _ _ Hlen, grpcReg_lookupL_snoc _ _ _ _ hfr,
        GMap.lookup_insert_eq_iff, HM x]
    · rw [Hregs', List.flatMap_append]; simp
    · rw [Hsregs', List.flatMap_append]; simp
    · intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact Hflag r hr
      · rw [List.mem_singleton] at hr
        subst hr
        exact Hst
  iapply BigSepL2.bigSepL2_snoc.2
  isplitl [Hregs]
  · iexact Hregs
  unfold srvRegIs
  isplitr
  · iexact Hdcopy
  iexists msl, ssl, stm, mdv, mls, M3
  isplitr
  · iexact Hmsl
  isplitr
  · iexact Hssl
  isplitl [Hinfo]
  · iexact Hinfo
  isplitl [Hstm]
  · iexact Hstm
  isplitl []
  · ipureintro
    refine ⟨Hmn, fun x => ?_⟩
    rw [HM3 x, grpcReg_srvStreamsL]
  iexact Hmls

end proof

end EtcdGrove
end Perennial
