/- Lean-first (no Rocq counterpart).

# `(*server).Echo`'s proof

Under the server's mutex: the request's value `v` is `mkVal id w` with `id`'s token; a nonzero count
at `v` would be of a value whose id's token the lock holds (`runsOk`), the same id (`mkVal_inj`),
two tokens of one id: so the count is `0`, the new count `1`, and the token goes into the lock
(`runsOk_insert`). The reply `v + "#" + FormatUint(1, 10)` is `v#1` (`fmtUint10_lt10`), below
`stringValueMax` (`v` is below `stringValueReqMax`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__Echo
public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String
public import Perennial.Spec.strconv.FormatUint
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem server.Echo.wp_proof (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG))
    (wp_String : google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG)) :
    server.Echo.spec (GF := GF) (hG := hG) := by
  intro γid s ctx r v md Φ Ψe
  wp_start as ⟨#Hs, Hrecv, Hspec⟩
  iunfold isDrvServer at Hs
  icases Hs with ⟨#Hpkg, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  isimp only [pbStringValueT, pbStringValue] at Hrecv
  icases Hrecv with ⟨%Hnn, %Hlen, #Hval⟩
  isimp only [echoSpec] at Hspec
  icases Hspec with ⟨%id, %w, %Hvw, Htok, HΦ'⟩
  obtain ⟨Hv, Hw⟩ := Hvw
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ (drvSrvInv γid s) $$ [$Hsync $Hmu] as ⟨Hlk, Hinv⟩
  iunfold drvSrvInv at Hinv
  icases Hinv with ⟨%mref, %m, %ids, Hruns, Hmap, %Hok, Htoks⟩
  -- the count at `v` is `0`: a nonzero one is of a value whose id's token the lock holds
  have hcase : (m !! v).getD (W64 0) = W64 0 ∨
      ∃ id' w', v = mkVal id' w' ∧ wordOk w' ∧ id' ∈ ids := by
    cases hm : m !! v with
    | none => exact Or.inl rfl
    | some n =>
      by_cases h0 : n = W64 0
      · exact Or.inl (by simp [h0])
      · exact Or.inr (Hok v n hm h0)
  rcases hcase with Hz | ⟨id', w', hv', hw', hmem⟩
  rotate_left
  · have hid : id = id' := mkVal_inj Hw hw' (Hv.symm.trans hv')
    subst hid
    icases BigSepL.bigSepL_mem_acc hmem $$ Htoks with ⟨Htok', -⟩
    iunfold idTok at Htok
    iunfold idTok at Htok'
    ihave %Hne := ghostMapElem_ne γid id id (DFrac.own 1) () () $$ Htok Htok'
    exact absurd rfl Hne
  try wp_auto
  have Hz' : (m !! v).getD (_root_.Perennial.zero_val w64) = W64 0 := by
    have h0 : (_root_.Perennial.zero_val w64) = W64 0 := by decide
    rw [h0]; exact Hz
  wp_apply wp_map_lookup1 $$ [Hmap] as Hmap
  · iexact Hmap
  first | rw [Hz'] | rw [Hz]
  try wp_auto
  wp_apply wp_mapInsert $$ [Hmap] as Hmap
  · iexact Hmap
  try wp_auto
  wp_apply wp_map_lookup1 $$ [Hmap] as Hmap
  · iexact Hmap
  rw [GMap.lookup_insert, Option.getD_some]
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ (drvSrvInv γid s) $$ [$Hsync $Hmu $Hlk Hruns Hmap Htoks Htok]
  · iunfold drvSrvInv
    iexists mref, _, id :: ids
    iframe Hruns Hmap
    isplitr
    · ipureintro; exact runsOk_insert Hok Hv Hw _
    simp only [BigSepL.bigSepL_cons]
    iframe
  try wp_auto
  have h1 : (W64 0 + W64 1 : w64) = W64 1 := by decide
  try rw [h1]
  wp_apply wp_FormatUint (W64 1) (W64 10) (by decide) (by decide) $$ [$Hsc]
  have hstr : v ++ go!"#" ++ internal.strconv.fmtUint (W64 1) (W64 10) = v ++ go!"#1" := by
    rw [internal.strconv.fmtUint10_lt10 _ (by decide), List.append_assoc]
    rfl
  try wp_auto
  rw [hstr]
  wp_apply wp_String (v ++ go!"#1") (by
      simp only [List.length_append, stringValueMax]
      have h2 : (go!"#1" : GoString).length = 2 := rfl
      have h29 : stringValueReqMax = 536870912 := by decide
      have h30 : (2 : Nat) ^ 30 = 1073741824 := by decide
      rw [h2, h30]
      rw [h29] at Hlen
      omega) as %l Hl
  try wp_auto
  iapply HΦ
  iframe
  ipureintro; rfl

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
