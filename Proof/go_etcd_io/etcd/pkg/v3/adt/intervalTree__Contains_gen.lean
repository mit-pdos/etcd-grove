/-
`intervalTree.Contains` (`interval_tree.go`) over a comparator: the proof of
`Spec/.../adt/intervalTree__Contains_gen.lean` (the auth plan's S2b, 2026-10-23): `Visit` with the
greedy scan as the visitor (`containsRes`, `Contains.lean`), which stops at a gap. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Contains_gen
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Visit_gen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `Contains`' scan state over the entries visited so far (`es`, in order): none visited, the
two `Comparable`s are `nil`; else `minBegin` holds the first's begin and `maxEnd` the scan's
running maximum, which has not broken. -/
def adt.cstate (K : adt.KeyRep (GF := GF)) (pmin pmax : Loc) : List adt.Entry → IProp GF
  | [] => iprop(pmin ↦ interface.nil ∗ pmax ↦ interface.nil)
  | z :: zs => iprop(∃ (me : GoString) (vmin vmax : val), ⌜adt.scanFrom z.1.2 zs = some me⌝ ∗
      pmin ↦ interface.mkOk K.ty vmin ∗ K.keyAt .discard vmin z.1.1 ∗
      pmax ↦ interface.mkOk K.ty vmax ∗ K.keyAt .discard vmax me)

theorem adt.cstate_nil (K : adt.KeyRep (GF := GF)) (pmin pmax : Loc) :
    adt.cstate K pmin pmax [] = iprop(pmin ↦ interface.nil ∗ pmax ↦ interface.nil) := rfl

theorem adt.cstate_cons (K : adt.KeyRep (GF := GF)) (pmin pmax : Loc) (z : adt.Entry)
    (zs : List adt.Entry) :
    adt.cstate K pmin pmax (z :: zs) =
      iprop(∃ (me : GoString) (vmin vmax : val), ⌜adt.scanFrom z.1.2 zs = some me⌝ ∗
        pmin ↦ interface.mkOk K.ty vmin ∗ K.keyAt .discard vmin z.1.1 ∗
        pmax ↦ interface.mkOk K.ty vmax ∗ K.keyAt .discard vmax me) := rfl

theorem adt.intervalTree.Contains_gen.wp_proof
    (h_Visit_gen : adt.intervalTree.Visit_gen.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Contains_gen.spec (GF := GF) (hG := hG) := by
  intro K hK t L vb ve db de b e dq
  wp_start as ⟨Ht, Hkb, Hke⟩
  ihave %hsorted := adt.ownIvtK_sorted K _ _ _ $$ Ht
  wp_auto
  have hz : ∀ a c, sint.Z (W64 (adt.affCmp a c)) = adt.affCmp a c := by
    intro a c; have := adt.affCmp_bounds a c; word
  have h0 : sint.Z (W64 0) = 0 := rfl
  -- the visitor's state: the scan over the entries visited (going on), or broken (stopped)
  let I : List (Loc × adt.Entry) → IProp GF := fun acc =>
    iprop(([∗list] x ∈ acc, K.ivAt x.1 dq x.2) ∗ isContiguous_ptr ↦ true ∗
      adt.cstate K minBegin_ptr maxEnd_ptr (acc.map Prod.snd))
  let J : List (Loc × adt.Entry) → IProp GF := fun acc =>
    iprop(([∗list] x ∈ acc, K.ivAt x.1 dq x.2) ∗ isContiguous_ptr ↦ false ∗
      ⌜∃ (z : adt.Entry) (zs : List adt.Entry), acc.map Prod.snd = z :: zs ∧
        adt.scanFrom z.1.2 zs = none⌝ ∗
      ∃ (vmin vmax : val) (mb me : GoString),
        minBegin_ptr ↦ interface.mkOk K.ty vmin ∗ K.keyAt .discard vmin mb ∗
        maxEnd_ptr ↦ interface.mkOk K.ty vmax ∗ K.keyAt .discard vmax me)
  wp_apply (h_Visit_gen K hK t L vb ve db de b e dq _ I J)
    $$ [Ht Hkb Hke minBegin maxEnd isContiguous] as ⟨Hkb, Hke, %ps, %es, %r, %hpl, HIJ, Hwand⟩
  · iframe Ht Hkb Hke
    isplitr [minBegin maxEnd isContiguous]
    · -- the visitor
      iunfold adt.ivVisitorOkK
      imodintro
      iintro %pv %z %acc %Φ'
      imodintro
      iintro ⟨%hpre, HIa, Hpv⟩ HΦ'
      icases HIa with ⟨Hacc, Hc, Hst⟩
      icases K.ivAt_open _ _ _ $$ Hpv with ⟨%zb, %ze, Hb, He, Hv, #Hkzb, #Hkze, Hpvb⟩
      cases hacc : acc.map Prod.snd with
      | nil =>
        (try simp only [hacc])
        simp only [adt.cstate_nil]
        icases Hst with ⟨Hmin, Hmax⟩
        wp_auto
        ihave Hpv := Hpvb $$ [Hb He Hv]
        · iframe
        ispecialize HΦ' $$ %true
        iapply HΦ'
        simp only [I, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, hacc,
          List.nil_append, adt.cstate_cons]
        iframe Hc
        isplitl [Hacc Hpv]
        · iapply BigSepL.bigSepL_snoc.2; iframe
        iexists z.1.2, zb, ze
        iframe ∗ #
        ipureintro; rfl
      | cons z0 zs0 =>
        (try simp only [hacc])
        simp only [adt.cstate_cons]
        icases Hst with ⟨%me, %vmin, %vmax, %hscan, Hmin, #Hkmin, Hmax, #Hkmax⟩
        wp_auto
        wp_apply hK .discard .discard vmax zb me z.1.1 $$ [] as ⟨-, -⟩
        · iframe ∗ #
        wp_if_destruct
        · -- a gap: the scan breaks, the visitor stops
          rw [hz, h0] at Hif
          (try wp_auto)
          ihave Hpv := Hpvb $$ [Hb He Hv]
          · iframe
          ispecialize HΦ' $$ %false
          iapply HΦ'
          simp only [J, Bool.false_eq_true, ↓reduceIte, List.map_append, List.map_cons,
            List.map_nil, hacc]
          iframe Hc
          isplitl [Hacc Hpv]
          · iapply BigSepL.bigSepL_snoc.2; iframe
          isplitl []
          · ipureintro
            refine ⟨z0, zs0 ++ [z], by simp, ?_⟩
            rw [adt.scanFrom_snoc, hscan]
            simp only [Hif, ↓reduceIte]
          iexists vmin, vmax, z0.1.1, me
          iframe ∗ #
        · -- the maximum, raised to the entry's end if above it
          rw [hz, h0] at Hif
          wp_apply hK .discard .discard ze vmax z.1.2 me $$ [] as ⟨-, -⟩
          · iframe ∗ #
          have hnext : adt.scanFrom z0.1.2 (zs0 ++ [z]) =
              some (if adt.affCmp z.1.2 me > 0 then z.1.2 else me) := by
            rw [adt.scanFrom_snoc, hscan]
            simp only [Hif, ↓reduceIte]
          wp_if_destruct
          · rw [hz, h0] at Hif
            (try wp_auto)
            ihave Hpv := Hpvb $$ [Hb He Hv]
            · iframe
            ispecialize HΦ' $$ %true
            iapply HΦ'
            simp only [I, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, hacc,
              List.cons_append, adt.cstate_cons]
            iframe Hc
            isplitl [Hacc Hpv]
            · iapply BigSepL.bigSepL_snoc.2; iframe
            iexists z.1.2, vmin, ze
            iframe ∗ #
            ipureintro
            rw [hnext]; simp only [show adt.affCmp z.1.2 me > 0 from Hif, ↓reduceIte]
          · rw [hz, h0] at Hif
            (try wp_auto)
            ihave Hpv := Hpvb $$ [Hb He Hv]
            · iframe
            ispecialize HΦ' $$ %true
            iapply HΦ'
            simp only [I, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, hacc,
              List.cons_append, adt.cstate_cons]
            iframe Hc
            isplitl [Hacc Hpv]
            · iapply BigSepL.bigSepL_snoc.2; iframe
            iexists me, vmin, vmax
            iframe ∗ #
            ipureintro
            rw [hnext]; simp only [show ¬ adt.affCmp z.1.2 me > 0 from Hif, ↓reduceIte]
    · -- the initial state
      simp only [I, List.map_nil, adt.cstate_nil]
      iframe
      iapply BigSepL.bigSepL_nil.2; itrivial
  -- after the visit: the result from the scan's state
  obtain ⟨hsub, hlen, hpq⟩ := hpl
  have hes : (ps.zip es).map Prod.snd = es := List.map_snd_zip (by omega)
  icases adt.ivl_split _ _ _ $$ ivl with ⟨Hivb, Hive, -⟩
  simp only [adt.KeyRep.ivl_Begin, adt.KeyRep.ivl_End]
  cases r with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, J] at hpq ⊢
    icases HIJ with ⟨Hacc, Hc, %hbroke, %vmin, %vmax, %mb, %me, Hmin, #Hkmin, Hmax, #Hkmax⟩
    rw [hes] at hbroke
    obtain ⟨z0, zs0, hes0, hnone⟩ := hbroke
    wp_auto
    iapply HΦ
    iframe Hkb Hke
    isplitl [Hacc Hwand]
    · iapply Hwand; iexact Hacc
    ipureintro
    intro hq
    obtain ⟨⟨t, ht⟩, -⟩ := hpq hq
    rw [hes0] at ht
    unfold adt.containsRes
    rw [← ht]
    simp only [List.cons_append, adt.scanFrom_none_append t zs0 _ hnone]
  | true =>
    simp only [↓reduceIte, I] at hpq ⊢
    icases HIJ with ⟨Hacc, Hc, Hst⟩
    rw [hes]
    cases hes' : es with
    | nil =>
      (try simp only [hes'])
      simp only [adt.cstate_nil]
      icases Hst with ⟨Hmin, Hmax⟩
      wp_auto
      iapply HΦ
      iframe Hkb Hke
      isplitl [Hacc Hwand]
      · iapply Hwand; iexact Hacc
      ipureintro
      intro hq
      have := hpq hq
      rw [hes'] at this
      unfold adt.containsRes
      rw [← this]
    | cons z zs =>
      (try simp only [hes'])
      simp only [adt.cstate_cons]
      icases Hst with ⟨%me, %vmin, %vmax, %hscan, Hmin, #Hkmin, Hmax, #Hkmax⟩
      wp_auto
      wp_apply hK .discard de vmax ve me e $$ [Hke] as ⟨-, Hke⟩
      · iframe ∗ #
      have hres : ∀ hq : (b = go!"" ∨ adt.affLt b e), adt.containsRes (b, e) L =
          decide (adt.affCmp me e ≥ 0 ∧ adt.affCmp z.1.1 b ≤ 0) := by
        intro hq
        have := hpq hq
        rw [hes'] at this
        unfold adt.containsRes
        rw [← this]
        dsimp only
        rw [hscan]
      wp_if_destruct
      · rw [hz, h0] at Hif
        wp_apply hK .discard db vmin vb z.1.1 b $$ [Hkb] as ⟨-, Hkb⟩
        · iframe ∗ #
        wp_if_destruct
        · rw [hz, h0] at Hif
          iapply HΦ
          iframe Hkb Hke
          isplitl [Hacc Hwand]
          · iapply Hwand; iexact Hacc
          ipureintro
          intro hq
          rw [hres hq]
          (try simp only [hz, h0])
          first
            | (rw [decide_eq_decide]; constructor <;> intro <;> omega)
            | (rw [eq_comm, decide_eq_false_iff_not]; intro h; omega)
            | (rw [eq_comm, decide_eq_true_eq]; omega)
        · rw [hz, h0] at Hif
          iapply HΦ
          iframe Hkb Hke
          isplitl [Hacc Hwand]
          · iapply Hwand; iexact Hacc
          ipureintro
          intro hq
          rw [hres hq]
          (try simp only [hz, h0])
          first
            | (rw [decide_eq_decide]; constructor <;> intro <;> omega)
            | (rw [eq_comm, decide_eq_false_iff_not]; intro h; omega)
            | (rw [eq_comm, decide_eq_true_eq]; omega)
      · rw [hz, h0] at Hif
        iapply HΦ
        iframe Hkb Hke
        isplitl [Hacc Hwand]
        · iapply Hwand; iexact Hacc
        ipureintro
        intro hq
        rw [hres hq]
        (try simp only [hz, h0])
        first
          | (rw [decide_eq_decide]; constructor <;> intro <;> omega)
          | (rw [eq_comm, decide_eq_false_iff_not]; intro h; omega)
          | (rw [eq_comm, decide_eq_true_eq]; omega)

end proof

end EtcdGrove
end Perennial
