/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/idutil/Generator__Next.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.idutil.Generator__Next
public import Spec.go_etcd_io.etcd.pkg.v3.idutil.lowbit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

/-- The 48 low bits of distinct suffixes below `2 ^ 48` apart, under a prefix with no low bits,
give distinct ids. -/
theorem idutil_id_inj (pfx s0 a b : BitVec 64) (hp : pfx &&& 0xffffffffffff#64 = 0#64)
    (_hs : s0 < 0x1000000000000#64) (ha : a < 0x1000000000000#64) (hb : b < 0x1000000000000#64)
    (h : pfx ||| ((s0 + a) &&& 0xffffffffffff#64) = pfx ||| ((s0 + b) &&& 0xffffffffffff#64)) :
    a = b := by
  have key : ∀ z : BitVec 64, (pfx ||| (z &&& 0xffffffffffff#64)) &&& 0xffffffffffff#64 =
      z &&& 0xffffffffffff#64 := by
    intro z
    rw [BitVec.and_or_distrib_right, hp, BitVec.zero_or, BitVec.and_assoc, BitVec.and_self]
  have h2 := congrArg (· &&& 0xffffffffffff#64) h
  simp only [key] at h2
  have h3 := congrArg BitVec.toNat h2
  have m := idutil_mask_toNat (s0 + a) 48 (by omega)
  have m' := idutil_mask_toNat (s0 + b) 48 (by omega)
  simp only [show (BitVec.ofNat 64 (2 ^ 48 - 1)) = 0xffffffffffff#64 from rfl] at m m'
  rw [m, m', BitVec.toNat_add, BitVec.toNat_add] at h3
  rw [BitVec.lt_def] at ha hb
  simp only [BitVec.toNat_ofNat] at ha hb
  apply BitVec.eq_of_toNat_eq
  omega

theorem w64_nat_lt48 (j : Nat) (h : j < 2 ^ 48) : W64 (j : Int) < 0x1000000000000#64 := by
  rw [BitVec.lt_def]
  have : (W64 (j : Int)).toNat = j := by
    unfold W64; simp only [BitVec.toNat_ofInt]; omega
  rw [this]; simp; omega

theorem w64_nat_inj (a b : Nat) (ha : a < 2 ^ 48) (hb : b < 2 ^ 48)
    (h : W64 (a : Int) = W64 (b : Int)) : a = b := by
  have h' := congrArg BitVec.toNat h
  unfold W64 at h'; simp only [BitVec.toNat_ofInt] at h'; omega

/-- The id issued `k + 1`-th is none of the first `k`. -/
theorem idIssued_not_new (pfx s0 : w64) (k : Nat) (Hs0 : uint.Z s0 < 2 ^ 48)
    (Hpl : pfx &&& W64 (2 ^ 48 - 1) = W64 0) (Hk : k + 1 < 2 ^ 48) :
    ¬ idIssued pfx s0 k (pfx ||| ((s0 + W64 ((k + 1 : Nat) : Int)) &&& W64 (2 ^ 48 - 1))) := by
  rintro ⟨j, hj1, hjk, heq⟩
  have hs : s0 < 0x1000000000000#64 := by
    rw [BitVec.lt_def]; simp [uint.Z] at Hs0 ⊢; omega
  have := idutil_id_inj pfx s0 _ _ Hpl hs (w64_nat_lt48 j (by omega)) (w64_nat_lt48 (k + 1) Hk)
    (by exact heq.symm)
  have := w64_nat_inj _ _ (by omega) Hk this
  omega

theorem idIssued_succ (pfx s0 : w64) (k : Nat) (id : w64) :
    idIssued pfx s0 (k + 1) id ↔
      idIssued pfx s0 k id ∨
        id = pfx ||| ((s0 + W64 ((k + 1 : Nat) : Int)) &&& W64 (2 ^ 48 - 1)) := by
  constructor
  · rintro ⟨j, hj1, hjk, heq⟩
    by_cases h : j = k + 1
    · subst h; exact Or.inr heq
    · exact Or.inl ⟨j, hj1, by omega, heq⟩
  · rintro (⟨j, hj1, hjk, heq⟩ | heq)
    · exact ⟨j, hj1, by omega, heq⟩
    · exact ⟨k + 1, by omega, Nat.le_refl _, heq⟩

/-- Issuing `nid` under the key `k`, whose generator is `g`, keeps the cluster's ids well formed (by
key since R2c; the key's entry a pair since stage 2). -/
theorem idClusterOk_issue {X : Type} (I : GMap w64 (Option IdClaimV)) (C : GMap IdKey IdKeyEntry)
    (R : GMap IdKey GName) (Fm : GMap IdKey X)
    (k : IdKey) (nid : w64) (L : List w64) (g : Loc) (Hok : idClusterOk I C R Fm)
    (HC : C !! k = some (L, some g)) (Hpn : idPfx nid = k.1) (HIn : I !! nid = none) :
    idClusterOk (I.insert nid none) (C.insert k (nid :: L, some g)) R Fm := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hok
  have hsome : ∀ k', ((C.insert k (nid :: L, some g)) !! k').isSome = (C !! k').isSome := by
    intro k'
    by_cases hk : k = k'
    · subst hk; rw [GMap.lookup_insert, HC]; rfl
    · rw [GMap.lookup_insert_ne _ _ hk]
  refine ⟨?_, ?_, ?_, ?_, fun k' => by rw [hsome]; exact h5 k', fun k' => by rw [hsome]; exact h6 k'⟩
  · intro id
    rw [GMap.lookup_insert_is_Some]
    by_cases h : nid = id
    · subst h
      simp only [true_or, true_iff]
      exact Or.inr ⟨k, (nid :: L, some g), GMap.lookup_insert _ _ _, List.mem_cons_self ..⟩
    · simp only [h, false_or, ne_eq, not_false_eq_true, true_and]
      rw [h1 id]
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨p, e, hp, hid⟩
        by_cases hpp : k = p
        · subst hpp
          rw [HC] at hp; cases hp
          exact ⟨k, (nid :: L, some g), GMap.lookup_insert _ _ _, List.mem_cons_of_mem _ hid⟩
        · exact ⟨p, e, by rw [GMap.lookup_insert_ne _ _ hpp]; exact hp, hid⟩
      · rintro ⟨p, e, hp, hid⟩
        by_cases hpp : k = p
        · subst hpp
          rw [GMap.lookup_insert] at hp; cases hp
          rcases List.mem_cons.1 hid with h' | h'
          · exact absurd h'.symm h
          · exact ⟨k, (L, some g), HC, h'⟩
        · exact ⟨p, e, by rw [GMap.lookup_insert_ne _ _ hpp] at hp; exact hp, hid⟩
  · intro p e hp
    by_cases hpp : k = p
    · subst hpp
      rw [GMap.lookup_insert] at hp; cases hp
      obtain ⟨g1, g2⟩ := h2 k (L, some g) HC
      refine ⟨g1, fun id hid => ?_⟩
      rcases List.mem_cons.1 hid with rfl | h'
      · exact Hpn
      · exact g2 id h'
    · rw [GMap.lookup_insert_ne _ _ hpp] at hp
      exact h2 p e hp
  · intro a b ea eb g' ha hb hga hgb
    have fix : ∀ c ec, (C.insert k (nid :: L, some g)) !! c = some ec →
        ∃ ec', C !! c = some ec' ∧ ec'.2 = ec.2 := by
      intro c ec hc
      by_cases hk : k = c
      · subst hk; rw [GMap.lookup_insert] at hc; cases hc; exact ⟨_, HC, rfl⟩
      · rw [GMap.lookup_insert_ne _ _ hk] at hc; exact ⟨ec, hc, rfl⟩
    obtain ⟨ea', ha', hea⟩ := fix a ea ha
    obtain ⟨eb', hb', heb⟩ := fix b eb hb
    exact h3 a b ea' eb' g' ha' hb' (by rw [hea]; exact hga) (by rw [heb]; exact hgb)
  · intro p e hp hne
    by_cases hpp : k = p
    · subst hpp; rw [GMap.lookup_insert] at hp; cases hp; rfl
    · rw [GMap.lookup_insert_ne _ _ hpp] at hp; exact h4 p e hp hne

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.idutil.Assumptions]

theorem idutil.Generator.Next.wp_proof [HasExt idIssueExt]
    (hL : idutil.lowbit.spec (GF := GF) (hG := hG)) :
    idutil.Generator.Next.spec (GF := GF) (hG := hG) := by
  intro γi g Φc
  wp_start as ⟨#Hg, Hc⟩
  -- the trusted model names the translation's struct type by its name (`idutil.model.Generator`)
  have hty : (idutil.model.Generator : go.GoType) = idutil.Generator.ty := by
    with_unfolding_all rfl
  have hlb : (idutil.model.lowbit : GoString) = idutil.lowbit := by with_unfolding_all rfl
  have hsl : (idutil.model.suffixLen : val) = idutil.suffixLen := by with_unfolding_all rfl
  simp only [hty, hlb, hsl]
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold idGen at Hg
  icases Hg with ⟨%s0, %Hgn, #Hpfx, %Hs0, #Hinv, %X, %hX, %Φs, %x, %HΦx, #Hkf, #Hcl⟩
  obtain ⟨Hs0, Hpl⟩ := Hs0
  -- the steps up to `atomic.AddUint64`'s resolution, one by one (`wp_auto` would take that step
  -- too, and its receipt with it)
  wp_alloc res_ptr as Hres
  wp_pures
  wp_alloc g_ptr as Hgl
  wp_pure
  wp_pure
  wp_load
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  -- the Go step resolving `atomic.AddUint64` gives one time receipt (D19b)
  wp_bind (App (Val (GoInstruction (FuncResolve _ _))) (Val _))
  iapply wp_go_step_receipt'
  case hv => exact isPanic_intoVal _
  inext
  iintro Hr -
  iapply wp_value'
  -- (R2c stage 2) step A, the increment: the id counted, pending, its wait slot taken
  wp_apply_core sync.atomic.wp_AddUint64 $$ [] [HΦ Hc Hgl Hr Hres]
  · iexact Hat
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%k, %L, %S, %P, >Hsuf, >Hcr, >Hcnt, >HS, >HP, >%Hdom⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists (s0 + W64 (k : Int))
  iframe Hsuf
  iintro Hsuf
  imod Hmask with -
  icases receipt_add_one_lt k $$ [Hr Hcr] with ⟨%Hlt, Hcr⟩
  · iframe
  iunfold idCred at Hc
  icases Hc with %Hb
  have Hk1 : k + 1 < 2 ^ 48 := Nat.lt_of_lt_of_le Hlt Hb
  have Hnew := idIssued_not_new γi.pfx s0 k Hs0 Hpl Hk1
  generalize hid : γi.pfx ||| ((s0 + W64 ((k + 1 : Nat) : Int)) &&& W64 (2 ^ 48 - 1)) = nid
    at Hnew
  have Hpn : idPfx nid = γi.pfx := by rw [← hid]; exact idPfx_or _ _ Hpl
  have HSn : S !! nid = none := by
    cases h : S !! nid with
    | none => rfl
    | some _ => exact absurd ((Hdom nid).2.1.mp (by simp [h])) Hnew
  have HPn : P !! nid = none := by
    cases h : P !! nid with
    | none => rfl
    | some _ => exact absurd ((Hdom nid).1.mp (Or.inr (by simp [h]))) Hnew
  imod ghost_map_insert nid () HSn $$ HS with ⟨HS, Hsl⟩
  imod ghost_map_insert nid () HPn $$ HP with ⟨HP, Hpd⟩
  imod Hclose $$ [Hsuf Hcr Hcnt HS HP] with -
  · inext
    iexists (k + 1), L, (S.insert nid ()), (P.insert nid ())
    have hsuf : s0 + W64 (k : Int) + W64 1 = s0 + W64 ((k + 1 : Nat) : Int) := by
      push_cast; word
    rw [hsuf]
    iframe Hsuf Hcr Hcnt HS HP
    ipureintro
    intro id'
    refine ⟨?_, ?_, ?_⟩
    · rw [idIssued_succ, ← (Hdom id').1, hid, GMap.lookup_insert_is_Some]
      by_cases h : nid = id'
      · subst h; simp
      · simp only [h, false_or, ne_eq, not_false_eq_true, true_and]
        constructor
        · rintro (h' | h')
          · exact Or.inl (Or.inl h')
          · exact Or.inl (Or.inr h')
        · rintro ((h' | h') | h')
          · exact Or.inl h'
          · exact Or.inr h'
          · exact absurd h'.symm h
    · rw [GMap.lookup_insert_is_Some, idIssued_succ, ← (Hdom id').2.1, hid]
      by_cases h : nid = id'
      · subst h; simp
      · constructor
        · rintro (h' | ⟨_, h'⟩)
          · exact absurd h' h
          · exact Or.inl h'
        · rintro (h' | h')
          · exact Or.inr ⟨h, h'⟩
          · exact absurd h'.symm h
    · intro hin
      rw [GMap.lookup_insert_ne _ _ (fun h => Hnew (by
        subst h; exact (Hdom nid).1.mp (Or.inl hin)))]
      exact (Hdom id').2.2 hin
  imodintro
  wp_auto
  wp_apply hL (s0 + W64 (k : Int) + W64 1) (W64 48) (by word)
  have hres : γi.pfx ||| ((s0 + W64 (k : Int) + W64 1) &&& W64 (2 ^ 48 - 1)) = nid := by
    rw [← hid]
    congr 2
    push_cast; word
  rw [hres]
  (try wp_auto)
  -- (R2c stage 2) step B, the issue: the record's `"Issue"` with both invariants open
  wp_bind (ExternalOp _ _ (Val _))
  iapply (wp_IdIssue nid g)
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%k', %L', %S', %P', >Hsuf, >Hcr, >Hcnt, >HS, >HP, >%Hdom'⟩
  iunfold idClusterInv at Hcl
  iinv Hcl with Hci Hclose2
  icases Hci with ⟨%I, %C, %R, %Fm, >HI, >HC, >HR, >HF, >%Hok, #HFs, >#HG⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iintro %b #Hfr
  imod Hmask with -
  cases b with
  | false =>
    -- another generator issued the id: nothing changes, and `assume` does not return
    imod Hclose2 $$ [HI HC HR HF] with -
    · inext
      iexists I, C, R, Fm
      iframe HI HC HR HF HFs HG
      ipureintro; exact Hok
    imod Hclose $$ [Hsuf Hcr Hcnt HS HP] with -
    · inext
      iexists k', L', S', P'
      iframe Hsuf Hcr Hcnt HS HP
      ipureintro; exact Hdom'
    imodintro
    wp_apply_core wp_assume
    iintro %h
    cases h
  | true =>
    ihave #Hf := Hfr $$ %rfl
    ihave #HfD : idIssueFragD nid g $$ []
    · rw [idIssueFragD_eq]; iexact Hf
    icombine HC Hcnt gives %HlkC
    have HlkC' : C !! γi.key = some (L', some g) := HlkC
    icombine HP Hpd gives %HlkP
    have HlkP' : P' !! nid = some () := HlkP
    -- the id is not yet issued: in no key's list, so in no map
    have HnL : nid ∉ L' := fun h => by rw [(Hdom' nid).2.2 h] at HlkP'; cases HlkP'
    have Hpok := (Hok.2.1 γi.key (L', some g) HlkC').1
    ihave %HIn : ⌜I !! nid = none⌝ $$ []
    · cases hI : I !! nid with
      | none => ipureintro; rfl
      | some v =>
        rcases (Hok.1 nid).1 (by simp [hI]) with h0 | ⟨k2, e2, hk2, hin⟩
        · exfalso
          rw [← hid] at h0
          exact idutil_or_ne_zero γi.pfx _ Hpok.1 h0
        · have hg2 := Hok.2.2.2.1 k2 e2 hk2 (List.ne_nil_of_mem hin)
          rcases e2 with ⟨L2, og2⟩
          cases og2 with
          | none => simp at hg2
          | some g2 =>
            icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := C)
              (Φ := fun k e => idKeyGenFacts (GF := GF) k e) hk2).1 $$ HG with ⟨Hk2, -⟩
            iunfold idKeyGenFacts at Hk2
            icases Hk2 with ⟨-, #Hl2⟩
            obtain ⟨n, hn⟩ := List.getElem?_of_mem hin
            ihave #Hf2 := (BigSepL.bigSepL_lookup (PROP := IProp GF)
              (Φ := fun _ id => idIssueFragD (L := hG.goose_localGS) id g2) hn) $$ Hl2
            ihave %Hgg := idIssueFragD_agree nid g2 g $$ Hf2 HfD
            subst Hgg
            have hkk := Hok.2.2.1 k2 γi.key (L2, some g2) (L', some g2) g2 hk2 HlkC' rfl rfl
            subst hkk
            rw [HlkC'] at hk2
            cases hk2
            exact absurd hin HnL
    imod ghost_map_insert nid (none : Option IdClaimV) HIn $$ HI with ⟨HI, Hu⟩
    imod ghost_map_update ((nid :: L', some g) : IdKeyEntry) $$ HC Hcnt with ⟨HC, Hcnt⟩
    imod ghost_map_delete $$ HP Hpd with HP
    imod Hclose2 $$ [HI HC HR HF] with -
    · inext
      iexists (I.insert nid none), (C.insert γi.key (nid :: L', some g)), R, Fm
      iframe HI HC HR HF
      isplitr
      · ipureintro
        exact idClusterOk_issue I C R Fm γi.key nid L' g Hok HlkC' Hpn HIn
      isplitl
      · iunfold idClaimsFacts at HFs
        iunfold idClaimsFacts
        have HIn' : I.lookup nid = none := HIn
        iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (m := I)
          (Φ := fun id v => idClaimFact Φs γi.fs id v) HIn').2
        iframe HFs
        iunfold idClaimFact
        itrivial
      · ihave ⟨Hk, HkC⟩ := (BigSepM.bigSepM_insert_acc (PROP := IProp GF) (m := C)
          (Φ := fun k e => idKeyGenFacts (GF := GF) k e) HlkC') $$ HG
        iapply HkC
        iunfold idKeyGenFacts at Hk
        iunfold idKeyGenFacts
        icases Hk with ⟨#Hpf, #Hl⟩
        simp only
        iframe Hpf
        iapply BigSepL.bigSepL_cons.2
        iframe HfD Hl
    imod Hclose $$ [Hsuf Hcr Hcnt HS HP] with -
    · inext
      iexists k', (nid :: L'), S', (P'.delete nid)
      iframe Hsuf Hcr Hcnt HS HP
      ipureintro
      intro id'
      refine ⟨?_, (Hdom' id').2.1, ?_⟩
      · rw [← (Hdom' id').1, List.mem_cons]
        by_cases h : nid = id'
        · subst h; simp [HlkP']
        · rw [GMap.lookup_delete_ne _ h]
          constructor
          · rintro ((h' | h') | h')
            · exact absurd h'.symm h
            · exact Or.inl h'
            · exact Or.inr h'
          · rintro (h' | h')
            · exact Or.inl (Or.inr h')
            · exact Or.inr h'
      · intro hin
        by_cases h : nid = id'
        · subst h; exact GMap.lookup_delete _ _
        · rw [GMap.lookup_delete_ne _ h]
          rcases List.mem_cons.1 hin with h' | h'
          · exact absurd h'.symm h
          · exact (Hdom' id').2.2 h'
    imodintro
    wp_apply_core wp_assume
    iintro -
    wp_auto
    iapply HΦ
    iunfold idFresh
    iunfold idUnclaimed
    iunfold idSlot
    iframe Hu Hsl
    isplitr
    · ipureintro; exact Hpn
    iexists γi.pfx, s0, (k + 1)
    iframe Hpfx
    ipureintro
    exact ⟨by omega, Hk1, hid.symm⟩

end proof

end EtcdGrove
end Perennial
