/-
`array.FreeCount`, `array.freePageIds`, `array.Init` (U2 internal): the `*array` implementation's
parts of `FLImpl.Contract` but `mergeSpans`.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__reindex

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

theorem arrayImpl_freeCount (a : Loc) : (arrayImpl (GF := GF) a).FreeCountSpec := by
  intro free
  dsimp only [arrayImpl]
  wp_start as ⟨%sl, Hf, Hids, Hcap⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hids
  wp_auto
  rw [show sl.len = W64 (free.length : Int) by word]
  iapply HΦ
  iexists sl
  iframe

theorem arrayImpl_freePageIds (a : Loc) : (arrayImpl (GF := GF) a).FreePageIdsSpec := by
  intro free
  dsimp only [arrayImpl]
  wp_start as ⟨%sl, Hf, Hids, Hcap⟩
  wp_auto
  iapply HΦ
  iframe
  iintro Hids
  iexists sl
  iframe

theorem arrayImpl_init (a : Loc) : (arrayImpl (GF := GF) a).InitSpec := by
  intro s fl ids xs Hwf _
  have hR := shared.reindex.wp_proof (arrayImpl (GF := GF) a) (arrayImpl_freePageIds a)
  dsimp only [arrayImpl]
  wp_start as ⟨#Hhdl, Hs, Hown, Hnew, Hnewcap⟩
  icases Hown with ⟨%sl, Hf, Hids, Hcap⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  iunfold ownShW at Hs
  icases Hs with ⟨%c, Hs, %Hok⟩
  wp_apply (hR s ({ fl with free := xs } : FLPg) c Hwf) $$ [Hs Hf Hnew Hnewcap] as ⟨Hs, Hown⟩
  · isplitl [Hs]
    · iExactEq Hs; rfl
    dsimp only [arrayImpl]
    iexists ids
    iframe
  iapply HΦ
  iframe

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
