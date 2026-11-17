module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__listItems
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.keyInScope
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__DeepCopyObject
public import Spec.maps.Keys
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PredOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ItemsRO

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input labelSel fieldSel)

section pure
variable [GooseExts]

/-- `listItems`' result over the keys `ks` visited (in order). -/
def itemsOfKeys (x : Input) (key : GoString) (m : RM) (ks : List GoString) : List Obj :=
  (((ks.filterMap fun k => (m.items !! k).map (k, ·)).filter fun ko =>
    keyInScopeL key x.Recursive' ko.1).filter fun ko => selOkL x ko.2).map Prod.snd

theorem listItemsL_keys (x : Input) (key : GoString) (m : RM) :
    listItemsL x key m = itemsOfKeys x key m (sortedKeysL m.items) := rfl

theorem itemsOfKeys_snoc (x : Input) (key : GoString) (m : RM) (ks : List GoString) (k : GoString)
    (o : Obj) (ho : m.items !! k = some o) :
    itemsOfKeys x key m (ks ++ [k]) = itemsOfKeys x key m ks ++
      (if keyInScopeL key x.Recursive' k && selOkL x o then [o] else []) := by
  have h1 : ([k].filterMap fun k => (m.items !! k).map (k, ·)) = [(k, o)] := by simp [ho]
  unfold itemsOfKeys
  simp only [List.filterMap_append, List.filter_append, List.map_append, h1]
  congr 1
  cases h1 : keyInScopeL key x.Recursive' k <;> cases h2 : selOkL x o <;> simp [h1, h2]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Model.listItems.wp_proof
    (wp_keyInScope : keyInScope.spec (GF := GF) (hG := hG))
    (wp_DeepCopy : k8s_etcd3.Obj.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_Keys : maps.Keys.spec_objMap (GF := GF) (hG := hG))
    (wp_SM : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) :
    Model.listItems.spec (GF := GF) (hG := hG) := by
  have wp_Matches := mlistMatches.wp_proof wp_SM wp_LM wp_LE wp_FM wp_FE wp_GA
  intro mp m x key
  wp_start as Hm
  unfold modelAt modelRep modelVal
  icases Hm with ⟨#Hinit, %il, %rl, %M, #Hp, #HI, #Hit, #HR⟩
  iStructNamed Hp
  wp_auto
  wp_apply (wp_Keys il) as %f #Hf
  -- BLOCKED (questions.md, "Step 3 STOP 2"): `maps.Keys.spec_objMap` returns `(f : val)`, which
  -- may be a panic value, so `let "$a0" := f` cannot step; the fix is `(f : GoFunc), RET #f`.
  sorry

end proof

end k8s_correctness
end EtcdGrove
end Perennial
