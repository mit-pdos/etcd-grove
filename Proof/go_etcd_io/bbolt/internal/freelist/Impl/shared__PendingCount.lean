/-
`shared.PendingCount()` (U2 internal).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.PendingCount()`: the number of pending ids. -/
abbrev shared.PendingCount.spec : Prop :=
  ∀ (s : Loc) (fli : GoInterface) (fl : FLPg) (c : GMap w64 Unit),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownShC s fli fl c }}
    (App (Val #(methods (go.GoType.PointerType shared.ty) go!"PendingCount" #s)) (Val #()))
  {{ RET #(W64 (fl.pendingIds.length : Int)); ownShC s fli fl c }}

theorem shared.PendingCount.wp_proof : shared.PendingCount.spec (GF := GF) (hG := hG) := by
  intro s fli fl c
  wp_start as Hsh
  iunfold ownShC at Hsh
  iNamed Hsh
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (tp : Loc),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ pp;fl.pending, ownPend p pd) ∗
      "count" ∷ count_ptr ↦
        W64 (((keys.take i.toNat).map (fun t => (fl.pendingOf t).ids.length)).sum : Int) ∗
      "txp" ∷ txp_ptr ↦ tp)) $$ Hpending
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hpds count txp]
  · iexists _
    simp only [Int.toNat_zero, List.take_zero, List.map_nil, List.sum_nil]
    iframe
    ipureintro; omega
  isplitr
  · imodintro
    iintro %i %key %p ⟨%Hkey, %Hp⟩ HP
    iNamed HP
    obtain ⟨pd, Hpd⟩ := Option.isSome_iff_exists.1
      ((Hdom key).1 (by simp only [show Std.get? pp key = some p from Hp, Option.isSome_some]))
    icases BigSepM2.bigSepM2_lookup_acc Hp Hpd $$ Hpds with ⟨Hpo, Hback⟩
    iunfold ownPend at Hpo
    icases Hpo with ⟨%Hpnn, Hpo⟩
    iunfold ownPending at Hpo
    icases Hpo with ⟨%ids, %atx, Hidsf, Hids, Hidc, Hatxf, Hatx, Hatxc, Hlrb⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hids
    wp_auto
    ihave Hpds := Hback $$ [Hidsf Hids Hidc Hatxf Hatx Hatxc Hlrb]
    · iunfold ownPend; isplitr
      · ipureintro; exact Hpnn
      iunfold ownPending; iexists ids, atx; iframe
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists p
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    have Hpo : (fl.pendingOf key).ids.length = pd.ids.length := by
      simp [FLPg.pendingOf, show fl.pending !! key = some pd from Hpd]
    rw [Htake, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Hpo, Nat.add_zero]
    have Hw : ∀ S : Nat, (W64 ((S + pd.ids.length : Nat) : Int) : w64) =
        W64 (S : Int) + ids.len := by intro S; word
    rw [Hw]
    iframe
    ipureintro; omega
  iintro HP Hpending
  iNamed HP
  rw [show (GMap.size pp : Int).toNat = keys.length by omega, List.take_length,
    pendingCount_keys fl keys (fun k => (Hkset k).trans (Hdom k)) Hknodup]
  wp_auto
  iapply HΦ
  iunfold ownShC
  iexists al, ca, pe, pp
  iframe

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
