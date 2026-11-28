/-
**The auth applier's `Put` at the latest state** (the auth plan's E2s; see
`AuthApplyLatest.lean`): `checkPutAuth` over the lease owner's resource (auth-lease S2: until then the
lessor finding no lease, `lookupNil`), its checks' verdicts at the latest state, the lease's
(`checkLeasePuts`, `leasePassedL`/`leaseRefusedL`) included, and `Put`'s outcome decided there
(`authOutLL` over `putPerms` and the put's lease).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthApplyLatest
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Keys

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`checkLeasePutsKeys` on the apply thread** (auth-lease S2): `checkLeasePutsKeys.spec`'s over the
store at the latest state, the verdict decided there: `nil` exactly when the lease passes
(`leasePassedL`: an admin, no revision check, or every key `I` attaches to `id` write-granted),
an error a refusal (`leaseRefusedL`). -/
abbrev apply.checkLeasePutsKeys.specL : Prop :=
  ∀ (st : GoInterface) (RD : IProp GF) (on : auth.AuthMode) (Lf : List auth.AuthState → IProp GF)
    (hs : List auth.AuthState)
    (ai : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (l : Loc) (id : w64)
    (γl : GName) (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (w : Option lease.LWin),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreL st RD on Lf ∗ ai ↦{dq} info ∗ lease.leaseOwnOpenW γl L I id l w ∗ RD ∗ Lf hs }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePutsKeys))
      (Val #st)) (Val #ai)) (Val #l))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ RD ∗ Lf hs ∗ lease.leaseOwnOpenW γl L I id l w ∗
      authApplyErrIs err ∗ ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.leaseKeysClass on info I id) ∗
      ⌜(err = GoInterface.nil → apply.leasePassedL on hs (auth.authInfoM info) I id) ∧
        (err ≠ GoInterface.nil → apply.leaseRefusedL on hs (auth.authInfoM info) I id)⌝ }}

/-- **`checkLeasePuts` on the apply thread** (auth-lease S2; until then `specNil`, the lessor finding
no lease): the owner's `Lookup(id)` (its resource lent and given back), then `checkLeasePutsKeys`'
verdict at the latest state; a lease the lessor does not have attaches no key and passes. -/
abbrev apply.checkLeasePuts.specL : Prop :=
  ∀ (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode) (Lf : List auth.AuthState → IProp GF)
    (hs : List auth.AuthState) (γl : GName) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)
    (ai : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (id : w64) (w : Option lease.LWin),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreL st RD on Lf ∗ txn.isTxnLessor le γl ∗ lease.lessorUserW γl L I w ∗
      ai ↦{dq} info ∗ RD ∗ Lf hs }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePuts))
      (Val #st)) (Val #ai)) (Val #le)) (Val #id))
  {{ (err : GoInterface), RET #err; lease.lessorUserW γl L I w ∗ ai ↦{dq} info ∗ RD ∗ Lf hs ∗
      authApplyErrIs err ∗ ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.leaseKeysClass on info I id) ∗
      ⌜(err = GoInterface.nil → apply.leasePassedL on hs (auth.authInfoM info) I id) ∧
        (err ≠ GoInterface.nil → apply.leaseRefusedL on hs (auth.authInfoM info) I id)⌝ }}

/-- **`checkPutAuth` on the apply thread**: `checkPutAuth.spec`'s over the lease owner's resource
(auth-lease S2: until then the lessor finding no lease), the verdict of the put's permissions and its
lease at the latest state. -/
abbrev apply.checkPutAuth.specL : Prop :=
  ∀ (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode) (Lf : List auth.AuthState → IProp GF)
    (hs : List auth.AuthState) (γl : GName) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (r : Loc) (o : OpFull) (w : Option lease.LWin),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreL st RD on Lf ∗ txn.isTxnLessor le γl ∗ lease.lessorUserW γl L I w ∗
      ai ↦{dq} info ∗ RD ∗ Lf hs ∗
      txn.putRequestIs r o }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkPutAuth))
      (Val #st)) (Val #ai)) (Val #le)) (Val #r))
  {{ (err : GoInterface), RET #err; lease.lessorUserW γl L I w ∗ ai ↦{dq} info ∗ RD ∗ Lf hs ∗
      authApplyErrIs err ∗ ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.putClass on info o ∗ apply.leaseKeysClass on info I o.leaseID) ∗
      ⌜(err = GoInterface.nil → apply.passedL on hs (auth.authInfoM info) (apply.putPerms o) ∧
          apply.leasePassedL on hs (auth.authInfoM info) I o.leaseID) ∧
        (err ≠ GoInterface.nil → apply.refusedL on hs (auth.authInfoM info) (apply.putPerms o) ∨
          apply.leaseRefusedL on hs (auth.authInfoM info) I o.leaseID)⌝ }}

/-- **`Put` on the apply thread**: `Put.spec`'s, the outcome decided at the latest state for the put's
permissions and its lease at the owner's item map of the log's state (`authOutLL`; auth-lease S2: until
then the lessor finding no lease, `authOutL` over `putPerms`); the certificates asked only of the
outcomes that verdict admits (`putPreW`, E3f). -/
abbrev apply.authApplierV3.Put.specL : Prop :=
  ∀ (E : apply.AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (rq : IRRModel)
    (o : OpFull) (log F : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (L : List auth.AuthState → IProp GF) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.authIs E p inner ∗ apply.authIsL E p L ∗ apply.applierSpec E c inner ∗
      apply.putPreW E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info r rq o log Pre Q Post
        (apply.authOutLL E.authMode hs (auth.authInfoM info) c rq log (apply.putPerms o)
          (mvcc.leaseItemsOf (mvcc.stateAfter log)) [o.leaseID]) ∗
      srvApi.kvLogLb E.γs F ∗ L hs ∗ apply.applyTok E }}
    (App (Val (p @!! go.GoType.PointerType authApplierV3.ty @!! go!"Put")) (Val #r))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      apply.kvPostFL E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info rq log F
        (apply.putAnswerIs log o resp err) Pre Post
        (apply.authOutLL E.authMode hs (auth.authInfoM info) c rq log (apply.putPerms o)
          (mvcc.leaseItemsOf (mvcc.stateAfter log)) [o.leaseID]) ∗
      L hs ∗ apply.traceRes trace ∗ apply.applyTok E }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `l.Keys()` by the owner: exactly the keys `I` attaches to `id`. -/
private theorem keys_open (hK : lease.Lease.Keys.spec (GF := GF) (hG := hG)) (γl : GName)
    (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64) (l : Loc)
    (w : Option lease.LWin) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
        lease.leaseOwnOpenW γl L I id l w }}
      (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.Lease.ty @!! go!"Keys"))
        (Val #()))
    {{ (sl : GoSlice), RET #sl; ∃ ks : List GoString, sl ↦* ks ∗ lease.leaseOwnOpenW γl L I id l w ∗
        ⌜∀ k ∈ ks, (k.length : Int) < 2 ^ 63 - 1⌝ ∗
        ⌜∀ k : GoString, k ∈ ks ↔
          I.lookup (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk k) = some id⌝ }} := by
  iintro %Φ ⟨#Hpkg, Ho⟩ HΦ
  iunfold lease.leaseOwnOpenW at Ho
  icases Ho with ⟨%HIS, #Hl, Hio, Hslot, Hback⟩
  iapply (hK γl l id (.owner I)) $$ [Hio Hslot]
  · iframe Hpkg Hl; rw [lease.keysPre_owner]; iframe Hio Hslot
  iintro !> %sl %ks ⟨Hs, Hpre, Hpost, %Hnd⟩
  ihave Hpre : iprop(lease.leaseItemsOwn l I id ∗
      sync.ownRWMutex (lease.lsF go!"mu" l) (lease.leaseItems γl l)) $$ [Hpre]
  · rw [← lease.keysPre_owner]; iexact Hpre
  icases Hpre with ⟨Hio, Hslot⟩
  ihave %Hks : ⌜∀ k : GoString, k ∈ ks ↔
      I.lookup (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk k) = some id⌝ $$ [Hpost]
  · rw [← lease.keysPost_owner]; iexact Hpost
  iapply HΦ
  iexists ks
  iframe Hs
  isplitl [Hio Hslot Hback]
  · iunfold lease.leaseOwnOpenW; iframe Hl Hio Hslot Hback; ipureintro; exact HIS
  ipureintro
  exact ⟨fun k hk => HIS _ id ((Hks k).1 hk), Hks⟩

private def keysPerms (ks : List GoString) : List apply.Perm3 := ks.map (fun k => (k, [], .write))

theorem apply.checkLeasePutsKeys.wp_latest (hK : lease.Lease.Keys.spec (GF := GF) (hG := hG)) :
    apply.checkLeasePutsKeys.specL (GF := GF) (hG := hG) := by
  intro st RD on Lf hs ai info dq l id γl L I w
  wp_start as ⟨#Hst, Hai, Hv, Hrd, HLf⟩
  ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  iunfold apply.isAuthStoreL at Hst
  icases Hst with ⟨%sti, %Hsti, #HPut, -, -, #HAdmin, #Hsnapf⟩
  subst Hsti
  ihave ⟨HLf, #Hsnap⟩ := Hsnapf $$ HLf
  wp_auto
  wp_apply HAdmin $$ [$Hai $Hrd $HLf] as %err ⟨Hai, Hrd, HLf, #HeI1, %Hadm⟩
  cases err with
  | nil =>
    wp_auto
    iapply HΦ; iframe Hai Hrd Hv HLf; isplitl []
    · iapply authApplyErrIs_nil
    isplitl []
    · ipureintro; intro _; rfl
    isplitl []
    · iintro %_
      cases on with
      | on γa =>
        unfold apply.leaseKeysClass
        ileft
        iunfold auth.latestSnap at Hsnap
        icases Hsnap with ⟨%i, %stl, %Hl, #Hs⟩
        iexists i, stl
        iframe Hs
        ipureintro
        exact (Hadm stl Hl).1 rfl
      | _ => unfold apply.leaseKeysClass; iintro; itrivial
    ipureintro
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    cases on with
    | on γa => intro stl hl; exact Or.inl ((Hadm stl hl).1 rfl)
    | off => trivial
    | any => trivial
  | ok e =>
  -- the admin check refused: not an admin at the latest state
  have Hnadm : apply.latestOk on hs (fun stl => ¬ auth.adminOk stl (some (auth.authInfoM info))) := by
    cases on with
    | on γa => intro stl hl h; cases (Hadm stl hl).2 h
    | off => cases Hadm
    | any => trivial
  have Hon : on.isOn = true ∨ on = .any := by
    cases on with
    | on γa => left; rfl
    | off => cases Hadm
    | any => right; rfl
  wp_auto
  wp_apply (keys_open hK γl L I id l w) $$ [$Hlp $Hv] as %sl ⟨%ks, Hks, Hv, %Hksb, %Hkall⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hks
  irename «as» => Has
  iunfold apply.permCheck2L at HPut
  ihave IH : iprop(∃ (n : w64) (k : GoString),
      "i" ∷ i_ptr ↦ n ∗ "key" ∷ key_ptr ↦ k ∗ "HLf" ∷ Lf hs ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝ ∗
      "%Hpass" ∷ ⌜apply.passedL on hs (auth.authInfoM info) (keysPerms (ks.take (sint.nat n)))⌝ ∗
      "#Hcls" ∷ apply.classRes on info (keysPerms (ks.take (sint.nat n)))) $$ [i key HLf]
  · iexists W64 0, _
    iframe i key HLf
    isplitl []
    · ipureintro
      constructor
      · decide
      · have := Hsll.2; word
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, show keysPerms [] = [] from rfl]
    isplitl []
    · ipureintro; exact apply.passedL_nil _ _ _
    iapply apply.classRes_nil
  wp_for IH
  wp_if_destruct
  · obtain ⟨kx, Hkx⟩ : ∃ kx, ks[(sint.Z n).toNat]? = some kx :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) _ _ kx Hn.1 $$ [Hks] as Hks
    · iframe; ipureintro; exact Hkx
    wp_apply wp_string_to_bytes kx as %bsl ⟨Hb, -⟩
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    have hkxI : I.lookup ⟨kx⟩ = some id := (Hkall kx).1 (List.mem_of_getElem? Hkx)
    wp_apply HPut $$ [$Hai $Hb $Hrd $HLf] as %err ⟨Hai, -, Hrd, HLf, #HeI2, %Hv2L, #Hv2⟩
    · ipureintro
      have h1 := Hksb kx (List.mem_of_getElem? Hkx)
      rw [Hbl.1] at h1
      have h3 := Hbl.2
      unfold sint.nat at h1
      word
    have Hone := apply.verdictL_one _ _ _ _ _ _ _ Hv2L
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, kx
      iframe
      have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by unfold sint.nat at *; word
      isplitl []
      · ipureintro; constructor <;> word
      rw [hsn, List.take_add_one, show ks[sint.nat n]? = some kx from Hkx, Option.toList_some]
      simp only [keysPerms, List.map_append, List.map_cons, List.map_nil]
      isplitl []
      · ipureintro
        exact apply.passedL_append _ _ _ _ _ Hpass (Hone.1 rfl)
      iapply apply.classRes_app
      iframe Hcls
      iapply (apply.classRes_of_permVerdict on info kx [] .write) $$ Hv2
    | ok e' =>
      wp_auto
      wp_for_post
      iapply HΦ; iframe Hai Hrd Hv HLf; isplitl []
      · iexact HeI2
      isplitl []
      · ipureintro; intro h; rcases Hon with h' | h'
        · rw [h] at h'; cases h'
        · subst h'; cases h
      isplitl []
      · iintro %h; cases h
      ipureintro
      refine ⟨(fun h => by cases h), fun _ => ?_⟩
      have hr := Hone.2 (fun h => by cases h)
      cases on with
      | on γa =>
        intro stl hl
        obtain ⟨x, hx, hn⟩ := hr stl hl
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨Hnadm stl hl, kx, hkxI, hn⟩
      | off => trivial
      | any => trivial
  iapply HΦ; iframe Hai Hrd Hv HLf; isplitl []
  · iapply authApplyErrIs_nil
  have hall : ks.take (sint.nat n) = ks := by
    apply List.take_of_length_le; unfold sint.nat at *; word
  rw [hall] at Hpass
  isplitl []
  · ipureintro; intro _; rfl
  isplitl []
  · iintro %_
    ihave #Hcls2 : apply.classRes (GF := GF) on info (keysPerms ks) $$ []
    · rw [show keysPerms ks = keysPerms (ks.take (sint.nat n)) by rw [hall]]; iexact Hcls
    unfold apply.leaseKeysClass
    cases on with
    | on γa =>
      iright
      iintro %k %hk
      have hmem : ((k, [], .write) : apply.Perm3) ∈ keysPerms ks := by
        unfold keysPerms; exact List.mem_map_of_mem ((Hkall k).2 hk)
      ihave #Hok : apply.classOk (GF := GF) γa info (keysPerms ks) $$ []
      · rw [← apply.classRes_on]; iexact Hcls2
      iapply (apply.classOk_of_mem γa info (keysPerms ks) (k, [], .write) hmem) $$ Hok
    | _ => iintro; itrivial
  ipureintro
  refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
  cases on with
  | on γa =>
    intro stl hl
    right
    intro k hk
    have hmem : ((k, [], .write) : apply.Perm3) ∈ keysPerms ks := by
      unfold keysPerms; exact List.mem_map_of_mem ((Hkall k).2 hk)
    exact Hpass stl hl _ hmem
  | off => trivial
  | any => trivial

theorem apply.checkLeasePuts.wp_latest
    (hKeys : apply.checkLeasePutsKeys.specL (GF := GF) (hG := hG)) :
    apply.checkLeasePuts.specL (GF := GF) (hG := hG) := by
  intro st le RD on Lf hs γl L I ai info dq id w
  wp_start as ⟨#Hst, #Htl, Hu, Hai, Hrd, HLf⟩
  ihave ⟨Hu, %HI⟩ := lease.lessorUserW_items γl L I w $$ Hu
  ihave #Htl' := Htl
  iunfold txn.isTxnLessor at Htl'
  icases Htl' with ⟨-, %li, %Hli, #HLookup, -⟩
  subst Hli
  wp_auto
  wp_apply HLookup $$ %id %L %I %w [$Hu] as %l ⟨Hu, %Hlid⟩
  have hnone : l = null → ∀ it, I.lookup it ≠ some id := by
    intro hl it hit
    exact (Hlid.1 hl) (HI.2 it id hit)
  by_cases hln : l = null
  · subst hln
    wp_auto
    iapply HΦ; iframe Hai Hrd HLf
    isplitl [Hu]
    · iapply lease.lessorUserOpenW_close $$ Hu
    isplitl []
    · iapply authApplyErrIs_nil
    isplitl []
    · ipureintro; intro _; rfl
    isplitl []
    · iintro %_
      iapply apply.leaseKeysClass_empty
      exact hnone rfl
    ipureintro
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    cases on with
    | on γa =>
      intro stl _; right; intro k hk; exact absurd hk (hnone rfl ⟨k⟩)
    | off => trivial
    | any => trivial
  · (try iunfold lease.lessorUserOpen at Hu); iunfold lease.lessorUserOpenW at Hu
    icases Hu with (⟨%Hn, -⟩ | ⟨Hrdl, Hrv, Ho⟩)
    · exact absurd Hn hln
    simp only [hln, decide_false, Bool.not_false]
    wp_auto
    wp_apply (hKeys st RD on Lf hs ai info dq l id γl L I w) $$ [$Hst $Hai $Hrd $Ho $HLf]
      as %err ⟨Hai, Hrd, HLf, Ho, #HeI, %Hoff, #Hcls, %Hvd⟩
    iapply HΦ; iframe Hai Hrd HeI Hcls HLf
    isplitl [Hrdl Hrv Ho]
    · iapply lease.lessorUserOpenW_close γl L I id l w
      iunfold lease.lessorUserOpenW
      iright
      iframe Hrdl Hrv Ho
    ipureintro; exact ⟨Hoff, Hvd⟩

theorem apply.checkPutAuth.wp_latest
    (hLP : apply.checkLeasePuts.specL (GF := GF) (hG := hG)) :
    apply.checkPutAuth.specL (GF := GF) (hG := hG) := by
  intro st le RD on Lf hs γl L I ai info dq r o w
  wp_start as ⟨#Hst, #Htl, Hu, Hai, Hrd, HLr, #Hr⟩
  ihave #Hst' := Hst
  iunfold apply.isAuthStoreL at Hst'
  icases Hst' with ⟨%sti, %Hsti, #HPut, #HRange, -⟩
  iunfold apply.permCheck2L at HPut
  iunfold apply.permCheck3L at HRange
  iunfold txn.putRequestIs at Hr
  icases Hr with ⟨%Hrn, %ksl, %vsl, %k, %v, %lease, %pk, %iv, %il, #HK, #Hk, -, -, #HL, #HPK, -, -, -, %Ho, %Hkb⟩
  subst Ho
  wp_auto
  rw [Hsti]
  wp_apply HPut $$ [$Hai $Hk $Hrd $HLr] as %err ⟨Hai, -, Hrd, HLr, #HeI1, %Hv1, #Hpv1⟩
  · ipureintro; exact Hkb
  have Hone1 := apply.verdictL_one _ _ _ _ _ _ _ Hv1
  have Hoff1 := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hv1
  cases err with
  | ok e =>
    wp_auto
    iapply HΦ; iframe Hu Hai Hrd HLr HeI1
    isplitl []
    · ipureintro; intro h; exact Hoff1 h
    isplitl []
    · iintro %h; cases h
    ipureintro
    refine ⟨(fun h => by cases h), fun _ => Or.inl ?_⟩
    simp only [apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base]
    exact apply.refusedL_append_left _ _ _ [(k, [], .write)] (if pk then [(k, [], .read)] else [])
      (Hone1.2 (fun h => by cases h))
  | nil =>
  wp_auto
  rw [← Hsti]
  wp_apply (hLP st le RD on Lf hs γl L I ai info dq lease w) $$ [$Hst $Htl $Hu $Hai $Hrd $HLr]
    as %err2 ⟨Hu, Hai, Hrd, HLr, #HeI2, %Hoff2, #Hlc, %Hvl⟩
  cases err2 with
  | ok e2 =>
    wp_auto
    iapply HΦ; iframe Hu Hai Hrd HLr HeI2
    isplitl []
    · ipureintro; intro h; exact Hoff2 h
    isplitl []
    · iintro %h; cases h
    ipureintro
    refine ⟨(fun h => by cases h), fun _ => Or.inr ?_⟩
    simpa [txn.putOpOf] using Hvl.2 (fun h => by cases h)
  | nil =>
  have Hlp : apply.leasePassedL on hs (auth.authInfoM info) I (txn.putOpOf k v lease pk iv il).leaseID := by
    simpa [txn.putOpOf] using Hvl.1 rfl
  ihave #Hlc := Hlc $$ %rfl
  wp_auto
  cases pk
  · wp_auto
    iapply HΦ; iframe Hu Hai Hrd HLr
    isplitl []
    · iapply authApplyErrIs_nil
    isplitl []
    · ipureintro; intro _; rfl
    isplitl []
    · iintro %_
      isplitl []
      · simp only [apply.putClass, apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base, Bool.false_eq_true, ↓reduceIte]
        iapply (apply.classRes_of_permVerdict on info k [] .write) $$ Hpv1
      · simp only [txn.putOpOf]; iexact Hlc
    ipureintro
    refine ⟨fun _ => ⟨?_, Hlp⟩, fun h => absurd rfl h⟩
    simp only [apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base, Bool.false_eq_true, ↓reduceIte]
    exact Hone1.1 rfl
  wp_auto
  ihave Hnil' := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  rw [Hsti]
  wp_apply HRange $$ %ai %info %dq %ksl %slice.nil %k %([] : List w8) %DFrac.discard %(DFrac.own 1) %hs [Hai Hnil' Hrd HLr]
    as %err ⟨Hai, -, -, Hrd, HLr, #HeI3, %Hv3, #Hpv3⟩
  · iframe; iframe #; try (ipureintro; exact Hkb)
  have Hone3 := apply.verdictL_one _ _ _ _ _ _ _ Hv3
  have Hoff3 := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hv3
  cases err with
  | ok e =>
    wp_auto
    iapply HΦ; iframe Hu Hai Hrd HLr HeI3
    isplitl []
    · ipureintro; intro h; exact Hoff3 h
    isplitl []
    · iintro %h; cases h
    ipureintro
    refine ⟨(fun h => by cases h), fun _ => Or.inl ?_⟩
    simp only [apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base, ↓reduceIte]
    exact apply.refusedL_append_right _ _ _ [(k, [], .write)] [(k, [], .read)]
      (Hone3.2 (fun h => by cases h))
  | nil =>
    wp_auto
    iapply HΦ; iframe Hu Hai Hrd HLr
    isplitl []
    · iapply authApplyErrIs_nil
    isplitl []
    · ipureintro; intro _; rfl
    isplitl []
    · iintro %_
      isplitl []
      · simp only [apply.putClass, apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base, ↓reduceIte]
        iapply apply.classRes_cons
        isplitl []
        · iapply (apply.classRes_of_permVerdict on info k [] .write) $$ Hpv1
        · iapply (apply.classRes_of_permVerdict on info k [] .read) $$ Hpv3
      · simp only [txn.putOpOf]; iexact Hlc
    ipureintro
    refine ⟨fun _ => ⟨?_, Hlp⟩, fun h => absurd rfl h⟩
    simp only [apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base, ↓reduceIte]
    exact apply.passedL_append _ _ _ [(k, [], .write)] [(k, [], .read)] (Hone1.1 rfl) (Hone3.1 rfl)

theorem apply.authApplierV3.Put.wp_latest
    (hPut : apply.checkPutAuth.specL (GF := GF) (hG := hG)) :
    apply.authApplierV3.Put.specL (GF := GF) (hG := hG) := by
  intro E c inner p r rq o log F Pre Q Post info L hs
  wp_start as ⟨#Hauth, #HauthL, #Hinner, Hpre, #HF, HL, Htt⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, -, ⟨%le, #Hlef, #Hle⟩, -⟩
  iunfold apply.isApplyLessor at Hle
  icases Hle with ⟨#Htl, -⟩
  iunfold apply.authIsL at HauthL
  icases HauthL with ⟨%st, #Hasf, #Hst⟩
  iunfold apply.putPreW at Hpre
  icases Hpre with ⟨%Hk, #Hr, %Lw, %Hwt, #Hcp, Hm⟩
  icases apply.mPreAt_split_chain _ _ _ _ _ _ _ _ _ $$ Hm with ⟨Hm, Hres⟩
  ihave ⟨Hard, Hu, Hkv⟩ := apply.mPreRestAt_lend E log Lw Pre Q Post $$ Hm
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner info $$ Happ Hres
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨#HI, -⟩
  have hk : apply.authChecks (dispatchKind rq) = true := by rw [Hk.2.1]; rfl
  wp_auto
  wp_apply (hPut st le E.RD E.authMode L hs (mvcc.api.mvccLeases E.γ) Lw
      (mvcc.leaseItemsOf (mvcc.stateAfter log)) _ info (DFrac.own 1) r o E.win)
    $$ [$Hst $Htl $Hu $Hinfo $Hard $HL $Hr] as %err ⟨Hu, Hinfo, Hard, HL, #HeI, %Hoff, #Hcls, %Hvd⟩
  ihave Hkv := Hkv $$ Hard Hu
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    iframe HL Htt
    isplitl
    rotate_left
    · iapply apply.traceRes_null
    ihave Hkv := apply.mPreRest_of_at _ _ _ _ _ _ $$ Hkv
    icases apply.mPreRest_reject_cs _ _ _ _ _ $$ Hkv with ⟨Hkv, %B, Hcs⟩
    iapply apply.auth_reject_kvPostFL E E.authOn c p (.ok bi) info rq log F _ _ Pre Q Post _ hk
      (Or.inl (by cases h : E.authOn <;> first | rfl | cases Hoff h))
      (Or.inl ⟨rfl, by
        rcases Hvd.2 (fun h => by cases h) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨o.leaseID, List.mem_singleton.2 rfl, h⟩⟩) $$ Happ [] Hkv Hinfo Hres Hcs
    simp only [apply.putAnswerIs, apply.putOutcomeIs, apply.rejErrIs]
    isplitr
    · ipureintro; trivial
    · iframe HeI; ipureintro; simp
  | nil =>
  wp_auto
  ihave ⟨#Hcls, #Hlk⟩ := Hcls $$ %rfl
  ihave #Hrc := apply.reqClass_put E.authMode info rq o Hk.1 Hk.2.1 $$ Hcls
  ihave #Hrl := apply.reqLeaseClass_put E.authMode info _ rq o Hk.1 Hk.2.1 $$ Hlk
  have Hpass : ∀ oc, apply.chainStep apply.backendStep c rq log oc →
      apply.authOutLL E.authMode hs (auth.authInfoM info) c rq log (apply.putPerms o)
        (mvcc.leaseItemsOf (mvcc.stateAfter log)) [o.leaseID] oc := by
    intro oc hoc
    obtain ⟨h1, h2⟩ := Hvd.1 rfl
    exact Or.inr ⟨hoc, h1, fun id hid => by rw [List.mem_singleton.1 hid]; exact h2⟩
  ihave #Hcp := apply.certPreW_innerT E E.authOn c rq log Lw
    (apply.authOutLL E.authMode hs (auth.authInfoM info) c rq log (apply.putPerms o)
      (mvcc.leaseItemsOf (mvcc.stateAfter log)) [o.leaseID])
    Hpass $$ Hcp
  iunfold apply.chainResAny at Hres
  icases Hres with ⟨%info', Hres⟩
  wp_apply HI $$ %r %rq %o %log %F %Pre %Q %Post %info' [Htt Hkv Hres] as %resp %trace %err ⟨Hpost, Htrc, Htt⟩
  · iframe Htt
    iunfold apply.putPre
    iframe #
    isplitr
    · ipureintro; exact Hk
    isplitr
    · ipureintro; exact Hwt (apply.pass_exists c rq log _ (apply.backendStep_exists_put rq log o Hk.1 Hk.2.1) Hpass)
    iapply apply.mPreAt_of_rest
    iframe
  iapply HΦ
  iframe HL Htt
  isplitr [Htrc]
  rotate_left
  · iexact Htrc
  iapply apply.auth_pass_kvPostFL E E.authOn c p (.ok bi) info info' rq log F _ Pre Post
    (apply.authOutLL E.authMode hs (auth.authInfoM info) c rq log (apply.putPerms o)
      (mvcc.leaseItemsOf (mvcc.stateAfter log)) [o.leaseID])
    Hpass $$ Happ Hpost Hinfo Hrc Hrl

end proof

end EtcdGrove
end Perennial
