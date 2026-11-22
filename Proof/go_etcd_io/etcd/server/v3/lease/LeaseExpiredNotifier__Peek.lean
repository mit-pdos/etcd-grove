/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/LeaseExpiredNotifier__Peek.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__Peek
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__Len

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.LeaseExpiredNotifier.Peek.wp_proof
    (hLen : lease.LeaseExpiredNotifier.Len.spec (GF := GF) (hG := hG)) :
    lease.LeaseExpiredNotifier.Peek.spec (GF := GF) (hG := hG) := by
  intro np q M
  wp_start as Hn
  wp_auto
  wp_apply (hLen np q M) $$ [$Hpkg $Hn] as ⟨Hn, %Hlt⟩
  (try wp_auto)
  by_cases h0 : M = ∅
  · have hs : GMap.size M = 0 := by rw [h0]; exact GMap.map_size_empty
    rw [hs]
    wp_auto
    iapply HΦ
    iframe Hn
    ileft; ipureintro; exact ⟨rfl, h0⟩
  · have hs : W64 (GMap.size M : Int) ≠ W64 0 := by
      intro h
      apply h0
      have : GMap.size M = 0 := by word
      exact (GMap.map_size_empty_iff M).1 this
    rw [decide_eq_false hs]
    wp_auto
    iunfold notifierAtM at Hn
    icases Hn with ⟨%mp, %s, %xs, Hm, HM, Hq, Hqa, %Hinv⟩
    iunfold queueAt at Hqa
    icases Hqa with ⟨Hs, Hcap, Hits⟩
    ihave %Hlen := ownSlice_len s _ _ $$ Hs
    obtain ⟨id0, p0, hp0⟩ : ∃ id p, M.lookup id = some p := by
      have hne : ¬ ∀ k, M !! k = none := fun h => h0 ((GMap.lookup_empty_iff M).1 h)
      obtain ⟨k, hk⟩ := Classical.not_forall.mp hne
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hk
      exact ⟨k, v, hv⟩
    have hxs : xs ≠ [] := by
      intro hx; have := (Hinv.2 id0 p0).1 hp0; rw [hx] at this; cases this
    obtain ⟨x0, xs', rfl⟩ := List.exists_cons_of_ne_nil hxs
    simp only [List.length_map, List.length_cons] at Hlen
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len := by constructor <;> word
    wp_auto
    try rw [if_pos hb]
    wp_apply wp_load_slice_index s (sint.Z (W64 0)) _ _ x0.1 hb.1 $$ [Hs] as Hs
    · iframe; ipureintro; rfl
    icases BigSepL.bigSepL_cons.1 $$ Hits with ⟨Hx0, Hits⟩
    iunfold lwtAt at Hx0
    icases Hx0 with ⟨#Hid, Ht0, Hix0⟩
    (try wp_auto)
    iapply HΦ
    isplitl [Hm HM Hq Hs Hcap Ht0 Hix0 Hits]
    · iunfold notifierAtM; iexists mp, s, (x0 :: xs')
      iframe Hm HM Hq
      isplitl [Hs Hcap Ht0 Hix0 Hits]
      · iunfold queueAt; iframe Hs Hcap; iapply BigSepL.bigSepL_cons.2; iframe Hits
        iunfold lwtAt; iframe Hid Ht0 Hix0
      ipureintro; exact Hinv
    iright
    iexists x0.2
    iframe Hid
    ipureintro
    exact (Hinv.2 x0.2 x0.1).2 (by simp)

end proof

end EtcdGrove
end Perennial
