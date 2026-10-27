/-
`getMergedPerms`'s proof (the auth plan's S2, 2026-10-23); see `InvAuth.lean`, `PermTree.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.getMergedPerms
public import Proof.go_etcd_io.etcd.server.v3.auth.PermTreeLemmas
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewIntervalTree
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewBytesAffineInterval
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewBytesAffinePoint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.getMergedPerms.wp_proof
    (h_NewIntervalTree : adt.NewIntervalTree.spec (GF := GF) (hG := hG))
    (h_NewBytesAffineInterval : adt.NewBytesAffineInterval.spec (GF := GF) (hG := hG))
    (h_NewBytesAffinePoint : adt.NewBytesAffinePoint.spec (GF := GF) (hG := hG)) :
    auth.getMergedPerms.spec (GF := GF) (hG := hG) := by
  intro ti Hs st name
  wp_start as ⟨#Hrd, Htok, %Hfit⟩
  ihave #Hadt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt $$ []
  · iPkgInit
  iunfold authReaderOk at Hrd
  icases Hrd with ⟨#HUG, #HGR, -, -, -⟩
  wp_auto
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #name))
  iapply HUG $$ Htok
  inext
  iintro %u ⟨Htok, Huser⟩
  wp_auto
  wp_if_destruct
  · -- no such user
    iunfold userOut at Huser
    cases hroles : st.users.lookup name with
    | some roles =>
      dsimp only
      icases Huser with ⟨%ur, %Hur, Huser⟩
      iunfold ownUser at Huser
      icases Huser with ⟨%ms, %nm, %pw, %rs, %o, %uf, %sc, Hu, -⟩
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hu
      exact absurd rfl Hnn
    | none =>
      dsimp only
      icases Huser with %Hu
      iapply HΦ
      iframe Htok
      ileft; ipureintro; exact ⟨rfl, rfl⟩
  · iunfold userOut at Huser
    cases hroles : st.users.lookup name with
    | none =>
      dsimp only
      icases Huser with %Hu
      exact absurd Hu Hif
    | some roles =>
      dsimp only
      icases Huser with ⟨%ur, %Hur, Huser⟩
      iunfold ownUser at Huser
      icases Huser with ⟨%ms, %nm, %pw, %rs, %o, %uf, %sc, Hu, -, -, #Hroles, -⟩
      obtain ⟨-, Hurr, -⟩ := Hur
      subst Hurr
      wp_apply h_NewIntervalTree as %tr Htr
      wp_apply h_NewIntervalTree as %tw Htw
      ihave Htr := adt.ownIvtB_of_empty tr $$ Htr
      ihave Htw := adt.ownIvtB_of_empty tw $$ Htw
      (try wp_auto)
      iclear Hu
      -- the roles loop: the trees hold the permissions of the roles seen so far
      ihave IH : iprop(∃ (n : w64) (rn : GoString) (Lr Lw : List adt.Entry),
          "i" ∷ i_ptr ↦ n ∗
          "roleName" ∷ roleName_ptr ↦ rn ∗
          "readPerms" ∷ readPerms_ptr ↦
            interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #tr ∗
          "writePerms" ∷ writePerms_ptr ↦
            interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #tw ∗
          "Htr" ∷ adt.ownIvtB tr Lr (DFrac.own 1) ∗
          "Htw" ∷ adt.ownIvtB tw Lw (DFrac.own 1) ∗
          "Htok" ∷ Hs st ∗
          "tx" ∷ tx_ptr ↦ GoInterface.ok ti ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ur.roles.length ∧
            (Lr.map Prod.fst).Perm (ivlsOf .read (userPerms st (ur.roles.take (sint.nat n)))) ∧
            (Lw.map Prod.fst).Perm (ivlsOf .write (userPerms st (ur.roles.take (sint.nat n))))⌝)
        $$ [i roleName readPerms writePerms Htr Htw Htok tx]
      · iexists W64 0, _, [], []
        iframe
        ipureintro
        have h0 : sint.nat (W64 0) = 0 := rfl
        refine ⟨by word, by word, ?_, ?_⟩ <;>
          (rw [show List.take (sint.nat (W64 0)) ur.roles = [] from rfl]; simp [ivlsOf, userPerms])
      iapply wp_fupd
      wp_for IH
      cleanup_bool_decide
      wp_if_destruct
      · -- another role
        have hlt : sint.Z n < sint.Z rs.len := by
          first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
        ihave %Hrl := ownSlice_len _ _ _ $$ Hroles
        have hn : sint.nat n < ur.roles.length := by rw [Hrl.1]; word
        obtain ⟨rn', hrn⟩ : ∃ x, ur.roles[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem hn⟩
        have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z rs.len := ⟨Hn.1, hlt⟩
        (try wp_auto)
        simp only [Hbnd, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index rs (sint.Z n) ur.roles .discard rn' Hn.1 $$ [$Hroles] as -
        · iframe; ipureintro; exact hrn
        (try wp_auto)
        wp_bind (App (Val #(methods ti.ty go!"UnsafeGetRole" ti.v)) (Val #rn'))
        iapply HGR $$ Htok
        inext
        iintro %r ⟨Htok, Hrole⟩
        (try wp_auto)
        wp_if_destruct
        · -- no such role: skipped
          iunfold roleOut at Hrole
          cases hps : st.roles.lookup rn' with
          | some ps =>
            dsimp only
            icases Hrole with ⟨%rr, %Hrr, Hr⟩
            iunfold ownRole at Hr
            icases Hr with ⟨%ms', %nm', %kp, %pps, %uf', %sc', Hr, -⟩
            ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hr
            exact absurd rfl Hnn
          | none =>
            dsimp only
            icases Hrole with -
            wp_for_post
            iframe HΦ «$res0»
            iexists n + W64 1, rn', Lr, Lw
            iframe
            ipureintro
            have hsucc : sint.nat (n + W64 1) = sint.nat n + 1 := by word
            rw [hsucc, userPerms_take_succ st ur.roles (sint.nat n) rn' hrn, hps]
            simp only [Option.getD_none, List.append_nil]
            exact ⟨by word, by omega, Hn.2.2.1, Hn.2.2.2⟩
        · iunfold roleOut at Hrole
          cases hps : st.roles.lookup rn' with
          | none =>
            dsimp only
            icases Hrole with %Hr
            exact absurd Hr Hif
          | some ps =>
            dsimp only
            icases Hrole with ⟨%rr, %Hrr, Hr⟩
            iunfold ownRole at Hr
            icases Hr with ⟨%ms', %nm', %kp, %pps, %uf', %sc', Hr, -, #Hkp, %Hplen, #Hperms⟩
            obtain ⟨-, Hrrps⟩ := Hrr
            ihave %Hkl := ownSlice_len _ _ _ $$ Hkp
            -- the outer counter, renamed before the inner loop's shadows it
            obtain ⟨io, hio⟩ : ∃ io, io = i_ptr := ⟨_, rfl⟩
            subst hio
            irename i => Hio
            (try wp_auto)
            iclear Hr
            -- the permissions loop: the trees hold the roles so far and this role's permissions so far
            ihave IH2 : iprop(∃ (m : w64) (pp : Loc) (Lr' Lw' : List adt.Entry),
                "i" ∷ i_ptr ↦ m ∗
                "perm" ∷ perm_ptr ↦ pp ∗
                "readPerms" ∷ readPerms_ptr ↦
                  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #tr ∗
                "writePerms" ∷ writePerms_ptr ↦
                  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #tw ∗
                "Htr" ∷ adt.ownIvtB tr Lr' (DFrac.own 1) ∗
                "Htw" ∷ adt.ownIvtB tw Lw' (DFrac.own 1) ∗
                "Htok" ∷ Hs st ∗
                "tx" ∷ tx_ptr ↦ GoInterface.ok ti ∗
                "Hio" ∷ io ↦ n ∗
                "roleName" ∷ roleName_ptr ↦ rn' ∗
                "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.nat m ≤ pps.length ∧
                  (Lr'.map Prod.fst).Perm (ivlsOf .read (userPerms st (ur.roles.take (sint.nat n)) ++
                    (rr.perms.take (sint.nat m)).filterMap permOfWire)) ∧
                  (Lw'.map Prod.fst).Perm (ivlsOf .write (userPerms st (ur.roles.take (sint.nat n)) ++
                    (rr.perms.take (sint.nat m)).filterMap permOfWire))⌝)
              $$ [i perm readPerms writePerms Htr Htw Htok tx Hio roleName]
            · iexists W64 0, _, Lr, Lw
              iframe
              ipureintro
              rw [show List.take (sint.nat (W64 0)) rr.perms = [] from rfl]
              simp only [List.filterMap_nil, List.append_nil]
              exact ⟨by word, by word, Hn.2.2.1, Hn.2.2.2⟩
            wp_for IH2
            cleanup_bool_decide
            wp_if_destruct
            · -- a permission
              have hlt2 : sint.Z m < sint.Z kp.len := by
                first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
              have hm : sint.nat m < pps.length := by rw [Hkl.1]; word
              obtain ⟨pp', hpp⟩ : ∃ x, pps[sint.nat m]? = some x := ⟨_, List.getElem?_eq_getElem hm⟩
              obtain ⟨w, hw⟩ : ∃ x, rr.perms[sint.nat m]? = some x :=
                ⟨_, List.getElem?_eq_getElem (by rw [← Hplen]; exact hm)⟩
              have Hbnd2 : 0 ≤ sint.Z m ∧ sint.Z m < sint.Z kp.len := ⟨Hm.1, hlt2⟩
              (try wp_auto)
              simp only [Hbnd2, _root_.and_self, ↓reduceIte]
              wp_apply wp_load_slice_index kp (sint.Z m) pps .discard pp' Hm.1 $$ [$Hkp] as -
              · iframe; ipureintro; exact hpp
              ihave #Hpw := BigSepL.bigSepL_lookup (Φ := fun (_ : Nat) (x : Loc × PermW) =>
                ownPermW (GF := GF) x.1 x.2) (l := pps.zip rr.perms) (i := sint.nat m) (x := (pp', w))
                (by rw [List.getElem?_zip_eq_some]; exact ⟨hpp, hw⟩) $$ Hperms
              iunfold ownPermW at Hpw
              icases Hpw with ⟨%Hppnn, %pms, %kk, %kre, %puf, %psc, #Hpp, #Hkk, #Hkre⟩
              dsimp only
              dsimp only at Hppnn
              obtain ⟨Hppnn, Hklen⟩ := Hppnn
              -- the message's fields
              icases typedPointsto_split _ _ _ $$ Hpp with Hpp
              simp only [TypedPointsto.typedPointstoDef]
              iNamed Hpp
              ihave %Hkrl := ownSlice_len _ _ _ $$ Hkre
              ihave %Hkkl := ownSlice_len _ _ _ $$ Hkk
              have hfit : (userPerms st ur.roles).length < 2 ^ 63 := Hfit name ur.roles hroles
              (try wp_auto)
              -- `rangeEnd`: `perm.RangeEnd`, unless it is `"\x00"` (then nil)
              wp_join iprop(∃ (re' : GoSlice) (es : GoString), rangeEnd_ptr ↦ re' ∗ perm_ptr ↦ pp' ∗
                  re' ↦*□ es ∗ ⌜es = if auth.isOpenEnded w.rangeEnd then [] else w.rangeEnd⌝)
                at next with [rangeEnd perm] as ⟨%re', %es, rangeEnd, perm, #Hre', %Hes⟩
              · (try wp_auto)
                wp_if_destruct
                · -- `len(RangeEnd) == 1`: the byte
                  have hl1 : w.rangeEnd.length = 1 := by rw [Hkrl.1, Hif]; rfl
                  obtain ⟨x, hx⟩ : ∃ x, w.rangeEnd[0]? = some x :=
                    ⟨_, List.getElem?_eq_getElem (by omega)⟩
                  have hre : w.rangeEnd = [x] := by
                    match w.rangeEnd, hl1, hx with
                    | [y], _, h => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; rw [h]
                  have Hbnd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z kre.len := by
                    rw [Hif]; decide
                  (try wp_auto)
                  simp only [Hbnd0, _root_.and_self, ↓reduceIte]
                  wp_apply wp_load_slice_index kre (sint.Z (W64 0)) w.rangeEnd .discard x (by decide)
                    $$ [$Hkre] as -
                  · iframe; ipureintro; exact hx
                  (try wp_auto)
                  wp_if_destruct
                  · -- `"\x00"`: nil
                    have ho : auth.isOpenEnded w.rangeEnd := by
                      unfold auth.isOpenEnded; rw [hre]; (try rw [Hif]); rfl
                    (try wp_auto)
                    wp_join_done
                    iexists slice.nil, []
                    iframe
                    (try isplitl []); (try iapply ownSlice_nil (V := w8) DFrac.discard)
                    ipureintro
                    simp [ho]
                  · -- not `0`: not open-ended
                    have hno : ¬ auth.isOpenEnded w.rangeEnd := by
                      intro h; rw [hre] at h; apply Hif; cases h; rfl
                    (try wp_auto)
                    wp_join_done
                    iexists kre, w.rangeEnd
                    iframe
                    (try isplitl []); (try iexact Hkre)
                    ipureintro
                    simp [hno]
                · -- `len(RangeEnd) != 1`: not open-ended
                  have hno : ¬ auth.isOpenEnded w.rangeEnd := by
                    intro h
                    have := congrArg List.length h
                    rw [Hkrl.1] at this
                    simp only [List.length_cons, List.length_nil] at this
                    apply Hif
                    word
                  (try wp_auto)
                  wp_join_done
                  iexists kre, w.rangeEnd
                  iframe
                  (try isplitl []); (try iexact Hkre)
                  ipureintro
                  simp [hno]
              -- `ivl`: the interval `[Key, rangeEnd)`, or the point when `RangeEnd` is empty
              wp_join iprop(∃ (e' : GoSlice) (es' : GoString) (dq : DFrac), ivl_ptr ↦ adt.bytesIvl kk e' ∗
                  perm_ptr ↦ pp' ∗ rangeEnd_ptr ↦ re' ∗ e' ↦*{dq} es' ∗
                  ⌜(w.key, es') = permIvl ⟨w.key, w.rangeEnd, .read⟩⌝)
                at next with [ivl perm rangeEnd] as ⟨%e', %es', %dq, ivl, perm, rangeEnd, He', %Hes'⟩
              · (try wp_auto)
                wp_if_destruct
                · -- a point
                  have h0 : w.rangeEnd = [] := (adt.slice_len_eq_zero Hkrl).1 Hif
                  (try wp_auto)
                  wp_apply (h_NewBytesAffinePoint kk w.key .discard) $$ [$Hkk] as %e ⟨-, He⟩
                  · ipureintro; rw [Hkkl.1] at Hklen; word
                  (try wp_auto)
                  wp_join_done
                  iexists e, w.key ++ [W8 0], DFrac.own 1
                  iframe
                  ipureintro
                  rw [h0, permIvl_point]
                · -- an interval
                  have hne : w.rangeEnd ≠ [] := fun h => Hif ((adt.slice_len_eq_zero Hkrl).2 h)
                  (try wp_auto)
                  wp_apply h_NewBytesAffineInterval
                  (try wp_auto)
                  wp_join_done
                  iexists re', es, DFrac.discard
                  iframe
                  (try isplitl []); (try iexact Hre')
                  ipureintro
                  rw [Hes]
                  by_cases ho : auth.isOpenEnded w.rangeEnd
                  · simp only [ho, ↓reduceIte]; rw [permIvl_open _ _ _ ho]
                  · simp only [ho, ↓reduceIte]; rw [permIvl_range _ _ _ hne ho]
              -- the permission's type: the trees it goes to
              (try wp_auto)
              wp_join iprop(∃ (Lr'' Lw'' : List adt.Entry),
                  adt.ownIvtB tr Lr'' (DFrac.own 1) ∗ adt.ownIvtB tw Lw'' (DFrac.own 1) ∗
                  readPerms_ptr ↦
                    interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #tr ∗
                  writePerms_ptr ↦
                    interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #tw ∗
                  ivl_ptr ↦ adt.bytesIvl kk e' ∗
                  ⌜(Lr''.map Prod.fst).Perm (ivlsOf .read (userPerms st (ur.roles.take (sint.nat n)) ++
                      ((rr.perms.take (sint.nat m)).filterMap permOfWire ++ (permOfWire w).toList))) ∧
                    (Lw''.map Prod.fst).Perm (ivlsOf .write (userPerms st (ur.roles.take (sint.nat n)) ++
                      ((rr.perms.take (sint.nat m)).filterMap permOfWire ++ (permOfWire w).toList)))⌝)
                with [Htr Htw readPerms writePerms ivl He']
                as ⟨%Lr'', %Lw'', Htr, Htw, readPerms, writePerms, ivl, %Hnew⟩
              · -- READWRITE: both trees
                have hpw := permOfWire_readwrite Hif
                imod ownSlice_persist _ _ _ $$ He' with #He'
                (try wp_auto)
                wp_apply (adt.intervalTree.wp_Insert_bytes tr Lr' kk e' w.key es' _) $$ [$Htr $Hkk $He']
                  as Htr
                · ipureintro
                  exact insert_count_ok st ur.roles _ _ rn' hfit hrn ps hps rr Hrrps w hw _ hpw _ Hm.2.2.1
                (try wp_auto)
                wp_apply (adt.intervalTree.wp_Insert_bytes tw Lw' kk e' w.key es' _) $$ [$Htw $Hkk $He']
                  as Htw
                · ipureintro
                  exact insert_count_ok st ur.roles _ _ rn' hfit hrn ps hps rr Hrrps w hw _ hpw _ Hm.2.2.2
                (try wp_auto)
                wp_join_done
                iexists _, _
                iframe
                ipureintro
                rw [hpw]
                simp only [Option.toList, ← List.append_assoc]
                rw [ivlsOf_append _ _ [_], ivlsOf_append _ _ [_], ivlsOf_singleton, ivlsOf_singleton]
                simp only [PermType.grants, PermType.grantsRead, PermType.grantsWrite,
                  Bool.false_eq_true, ↓reduceIte, List.append_nil]
                rw [permIvl_ty w.key w.rangeEnd _ .read, ← Hes']
                exact ⟨perm_insert_snoc Hm.2.2.1 _, perm_insert_snoc Hm.2.2.2 _⟩
              · have Hif2 := Hif
                wp_if_destruct
                · -- READ
                  have hpw := permOfWire_read Hif
                  imod ownSlice_persist _ _ _ $$ He' with #He'
                  (try wp_auto)
                  wp_apply (adt.intervalTree.wp_Insert_bytes tr Lr' kk e' w.key es' _) $$ [$Htr $Hkk $He']
                    as Htr
                  · ipureintro
                    exact insert_count_ok st ur.roles _ _ rn' hfit hrn ps hps rr Hrrps w hw _ hpw _ Hm.2.2.1
                  (try wp_auto)
                  wp_join_done
                  iexists _, _
                  iframe
                  ipureintro
                  rw [hpw]
                  simp only [Option.toList, ← List.append_assoc]
                  rw [ivlsOf_append _ _ [_], ivlsOf_append _ _ [_], ivlsOf_singleton, ivlsOf_singleton]
                  simp only [PermType.grants, PermType.grantsRead, PermType.grantsWrite,
                    Bool.false_eq_true, ↓reduceIte, List.append_nil]
                  rw [permIvl_ty w.key w.rangeEnd _ .read, ← Hes']
                  exact ⟨perm_insert_snoc Hm.2.2.1 _, Hm.2.2.2⟩
                · have Hif1 := Hif
                  wp_if_destruct
                  · -- WRITE
                    have hpw := permOfWire_write Hif
                    imod ownSlice_persist _ _ _ $$ He' with #He'
                    (try wp_auto)
                    wp_apply (adt.intervalTree.wp_Insert_bytes tw Lw' kk e' w.key es' _) $$ [$Htw $Hkk $He']
                      as Htw
                    · ipureintro
                      exact insert_count_ok st ur.roles _ _ rn' hfit hrn ps hps rr Hrrps w hw _ hpw _ Hm.2.2.2
                    (try wp_auto)
                    wp_join_done
                    iexists _, _
                    iframe
                    ipureintro
                    rw [hpw]
                    simp only [Option.toList, ← List.append_assoc]
                    rw [ivlsOf_append _ _ [_], ivlsOf_append _ _ [_], ivlsOf_singleton, ivlsOf_singleton]
                    simp only [PermType.grants, PermType.grantsRead, PermType.grantsWrite,
                      Bool.false_eq_true, ↓reduceIte, List.append_nil]
                    rw [permIvl_ty w.key w.rangeEnd _ .read, ← Hes']
                    exact ⟨Hm.2.2.1, perm_insert_snoc Hm.2.2.2 _⟩
                  · -- an unknown type: nothing
                    have hpw := permOfWire_none Hif1 Hif Hif2
                    (try wp_auto)
                    wp_join_done
                    iexists Lr', Lw'
                    iframe
                    ipureintro
                    rw [hpw]
                    simp only [Option.toList, List.append_nil]
                    exact ⟨Hm.2.2.1, Hm.2.2.2⟩
              -- the next permission
              wp_for_post
              iframe HΦ «$res0»
              iexists m + W64 1, pp', Lr'', Lw''
              iframe
              ipureintro
              have hsucc : sint.nat (m + W64 1) = sint.nat m + 1 := by
                have := Hkl.1; have := Hkl.2; word
              rw [hsucc, filterMap_take_succ permOfWire rr.perms (sint.nat m) w hw]
              exact ⟨by word, by omega, Hnew.1, Hnew.2⟩
            · -- the role's permissions are in the trees
              have hge2 : ¬ sint.Z m < sint.Z kp.len := by
                first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
              have hmlen : sint.nat m = pps.length := by
                have := Hm.2.1; rw [Hkl.1] at this ⊢; have := Hkl.2; word
              wp_for_post
              iframe HΦ «$res0»
              iexists n + W64 1, rn', Lr', Lw'
              iframe
              ipureintro
              have hsucc : sint.nat (n + W64 1) = sint.nat n + 1 := by
                have := Hrl.1; have := Hrl.2; word
              have hall : (rr.perms.take (sint.nat m)).filterMap permOfWire = ps := by
                rw [hmlen, Hplen, List.take_length, ← Hrrps]; rfl
              rw [hall] at Hm
              rw [hsucc, userPerms_take_succ st ur.roles (sint.nat n) rn' hrn, hps, Option.getD_some]
              exact ⟨by word, by omega, Hm.2.2.1, Hm.2.2.2⟩
      · have hge : ¬ sint.Z n < sint.Z rs.len := by
          first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
        ihave %Hrl := ownSlice_len _ _ _ $$ Hroles
        have hlen : sint.nat n = ur.roles.length := by
          have := Hn.2.1; rw [Hrl.1] at this ⊢; word
        rw [hlen, List.take_length] at Hn
        -- the trees are complete: read-only from now on
        imod (adt.ownIvtB_persist tr Lr) $$ Htr with #Htr
        imod (adt.ownIvtB_persist tw Lw) $$ Htw with #Htw
        irename «$r0» => Hp
        generalize «$r0_ptr» = p at *
        ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hp
        icases typedPointsto_split _ _ _ $$ Hp with Hp
        simp only [TypedPointsto.typedPointstoDef]
        iNamed Hp
        imod adt.tp_persist _ _ _ $$ readPerms with #readPerms
        imod adt.tp_persist _ _ _ $$ writePerms with #writePerms
        imodintro
        iapply HΦ
        iframe Htok
        iright
        iexists Lr, Lw
        isplitl []
        · iunfold permsAt
          isplitl []
          · ipureintro; exact Hpnn
          iexists tr, tw
          isplitl []
          · iexact readPerms
          isplitl []
          · iexact writePerms
          isplitl []
          · iexact Htr
          iexact Htw
        ipureintro
        exact ⟨ur.roles, hroles, Hn.2.2.1, Hn.2.2.2⟩

end proof

end EtcdGrove
end Perennial
