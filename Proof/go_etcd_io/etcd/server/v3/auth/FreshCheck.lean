/-
**The permission checks no older than a reader's lower bound** (the auth plan's E3h, 2026-10-27;
`notes/decisions.md`, "E3h of the auth plan"). Lean-first (no Rocq counterpart).

A reader holding a lower bound `n` of the published index (`authPubLbM`, E3g) reads the store's
fields fresh (`Fresh.lean`: the flag `IsAuthEnabled.specLb`, the revision `Revision.specLb`; here
the permission cache, `cacheFresh`) and the backend (`lockedReadTx.specLb`, `ReadLb.lean`). Here:
the verdicts no older than `n` (`cacheVerdictFrom`, `permVerdictFrom`: S3's verdicts, each of its
recorded states at an index at least `n`), their lemmas (as `VerdictLemmas.lean`'s), and the
checks' specs `isRangeOpPermitted.specLb` and `isOpPermitted.specLb`, beside today's.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Fresh
public import Proof.go_etcd_io.etcd.server.v3.auth.ReadLb
public import Proof.go_etcd_io.etcd.server.v3.auth.Latest
public import Proof.go_etcd_io.etcd.server.v3.auth.VerdictLemmas
public import Spec.go_etcd_io.etcd.server.v3.auth.checkKeyInterval
public import Spec.go_etcd_io.etcd.server.v3.auth.checkKeyPoint
public import Spec.go_etcd_io.etcd.server.v3.auth.hasRootRole
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.ByteString
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Error

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- The view's four states recorded at indices at least `n` (persistent). -/
def recordedVFrom (γa : AuthNames) (n : Nat) (v : AuthView) : IProp GF :=
  iprop((∃ i : Nat, authStateAt γa i v.flag ∗ ⌜n ≤ i⌝) ∗ (∃ i : Nat, authStateAt γa i v.rev ∗ ⌜n ≤ i⌝) ∗
    (∃ i : Nat, authStateAt γa i v.user ∗ ⌜n ≤ i⌝) ∗ (∃ i : Nat, authStateAt γa i v.cache ∗ ⌜n ≤ i⌝))

instance recordedVFrom_persistent (γa : AuthNames) (n : Nat) (v : AuthView) :
    Persistent (recordedVFrom (GF := GF) γa n v) := by
  unfold recordedVFrom; infer_instance

theorem recordedVFrom_intro (γa : AuthNames) (n i j k l : Nat) (a b c d : AuthState)
    (h : n ≤ i ∧ n ≤ j ∧ n ≤ k ∧ n ≤ l) :
    authStateAt (GF := GF) γa i a ⊢ authStateAt γa j b -∗ authStateAt γa k c -∗
      authStateAt γa l d -∗ recordedVFrom γa n ⟨a, b, c, d⟩ := by
  unfold recordedVFrom
  iintro Ha Hb Hc Hd
  isplitl [Ha]
  · iexists i; iframe Ha; ipureintro; exact h.1
  isplitl [Hb]
  · iexists j; iframe Hb; ipureintro; exact h.2.1
  isplitl [Hc]
  · iexists k; iframe Hc; ipureintro; exact h.2.2.1
  · iexists l; iframe Hd; ipureintro; exact h.2.2.2

theorem recordedVFrom_diag (γa : AuthNames) (n i : Nat) (st : AuthState) (h : n ≤ i) :
    authStateAt (GF := GF) γa i st ⊢ recordedVFrom γa n ⟨st, st, st, st⟩ := by
  iintro #H
  iapply (recordedVFrom_intro γa n i i i i st st st st ⟨h, h, h, h⟩) $$ H H H H

/-- **A permission check's verdict no older than the index `n`** in the mode `M` (persistent):
`permVerdict`, each of its recorded states at an index at least `n`. -/
def permVerdictFrom (M : AuthMode) (n : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (key rangeEnd : GoString) (op : PermType) (err : GoInterface) : IProp GF :=
  match M with
  | .off => iprop(⌜err = GoInterface.nil⌝)
  | .any => iprop(True)
  | .on γa =>
      iprop((∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
          ⌜n ≤ i ∧ (err = GoInterface.nil → permitted st (authInfoM info) key rangeEnd op)⌝) ∗
        (∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
          ⌜n ≤ i ∧ (err = GoInterface.nil → st.enabled = false ∨ st.revision ≤ (authInfoM info).rev)⌝) ∗
        (∃ v : AuthView, recordedVFrom γa n v ∗
          ⌜err ≠ GoInterface.nil → refusedV v (authInfoM info) key rangeEnd op⌝))

instance permVerdictFrom_persistent (M : AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) (op : PermType)
    (err : GoInterface) : Persistent (permVerdictFrom (GF := GF) M n info key rangeEnd op err) := by
  unfold permVerdictFrom; cases M <;> infer_instance

/-- A verdict no older than an index is a verdict. -/
theorem permVerdictFrom_verdict (M : AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) (op : PermType)
    (err : GoInterface) :
    permVerdictFrom (GF := GF) M n info key rangeEnd op err ⊢ permVerdict M info key rangeEnd op err := by
  cases M with
  | off => simp only [permVerdictFrom, permVerdict]; iintro H; iexact H
  | any => simp only [permVerdictFrom, permVerdict]; iintro -; itrivial
  | on γa =>
    simp only [permVerdictFrom, permVerdict, recordedVFrom]
    iintro ⟨⟨%i, %st, #H1, %Hp1⟩, ⟨%j, %sr, #H2, %Hp2⟩, ⟨%v, ⟨⟨%a, #Ha, -⟩, ⟨%b, #Hb, -⟩,
      ⟨%c, #Hc, -⟩, ⟨%d, #Hd, -⟩⟩, %Hv⟩⟩
    isplitr
    · iexists i, st; iframe H1; ipureintro; exact Hp1.2
    isplitr
    · iexists j, sr; iframe H2; ipureintro; exact Hp2.2
    iexists v
    isplitr
    · iapply (recordedV_intro γa a b c d v.flag v.rev v.user v.cache) $$ Ha Hb Hc Hd
    · ipureintro; exact Hv

/-- **`isRangeOpPermitted`'s verdict no older than the index `n`** in the mode `M` (persistent): in
`on γa`, the verdict at the cache's state (`cacheVerdictP`) of a state recorded at an index at least
`n`; otherwise nothing. -/
def cacheVerdictFrom (M : AuthMode) (n : Nat) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (b : Bool) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (i : Nat) (sta : AuthState), authStateAt γa i sta ∗
      ⌜n ≤ i ∧ cacheVerdictP sta user k e pt b⌝)
  | _ => iprop(True)

instance cacheVerdictFrom_persistent (M : AuthMode) (n : Nat) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (b : Bool) :
    Persistent (cacheVerdictFrom (GF := GF) M n user k e pt b) := by
  unfold cacheVerdictFrom; cases M <;> infer_instance

/-- **The cache's map, fresh** (persistent): in `on γa`, the cache of a state recorded at an index
at least `n`; otherwise the guard's entries (`cacheOk`). -/
def cacheFrom (M : AuthMode) (n : Nat) (Mp : GMap GoString Loc) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (i : Nat) (sta : AuthState), authStateAt γa i sta ∗ ⌜n ≤ i⌝ ∗ cacheOf sta Mp)
  | _ => iprop([∗map] _u ↦ p ∈ Mp, ∃ Lr Lw, permsAt p Lr Lw)

set_option synthInstance.maxSize 512 in
instance cacheFrom_persistent (M : AuthMode) (n : Nat) (Mp : GMap GoString Loc) :
    Persistent (cacheFrom (GF := GF) M n Mp) := by
  unfold cacheFrom; cases M <;> infer_instance

/-- A cache entry's model no older than `n`. -/
def entryFrom (M : AuthMode) (n : Nat) (user : GoString) (Lr Lw : List adt.Entry) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (i : Nat) (sta : AuthState), authStateAt γa i sta ∗
      ⌜n ≤ i ∧ cacheEntryIs sta user Lr Lw⌝)
  | _ => iprop(True)

instance entryFrom_persistent (M : AuthMode) (n : Nat) (user : GoString) (Lr Lw : List adt.Entry) :
    Persistent (entryFrom (GF := GF) M n user Lr Lw) := by
  unfold entryFrom; cases M <;> infer_instance

set_option synthInstance.maxSize 512 in
theorem cacheFrom_lookup (M : AuthMode) (n : Nat) (Mp : GMap GoString Loc) (user : GoString)
    (p : Loc) (h : Mp !! user = some p) :
    cacheFrom (GF := GF) M n Mp ⊢ ∃ Lr Lw, permsAt p Lr Lw ∗ entryFrom M n user Lr Lw := by
  cases M with
  | on γa =>
    unfold cacheFrom entryFrom cacheOf
    iintro ⟨%i, %sta, #Hst, %Hn, -, Hall⟩
    ihave #Hp := BigSepM.bigSepM_lookup (Φ := fun (u : GoString) (p : Loc) =>
      iprop(∃ Lr Lw, permsAt (GF := GF) p Lr Lw ∗ ⌜cacheEntryIs sta u Lr Lw⌝)) h $$ Hall
    icases Hp with ⟨%Lr, %Lw, #Hp, %Hent⟩
    iexists Lr, Lw
    iframe Hp
    iexists i, sta
    iframe Hst
    ipureintro; exact ⟨Hn, Hent⟩
  | off =>
    unfold cacheFrom entryFrom
    iintro Hall
    ihave #Hp := BigSepM.bigSepM_lookup (Φ := fun (_ : GoString) (p : Loc) =>
      iprop(∃ Lr Lw, permsAt (GF := GF) p Lr Lw)) h $$ Hall
    icases Hp with ⟨%Lr, %Lw, #Hp⟩
    iexists Lr, Lw
    iframe Hp
  | any =>
    unfold cacheFrom entryFrom
    iintro Hall
    ihave #Hp := BigSepM.bigSepM_lookup (Φ := fun (_ : GoString) (p : Loc) =>
      iprop(∃ Lr Lw, permsAt (GF := GF) p Lr Lw)) h $$ Hall
    icases Hp with ⟨%Lr, %Lw, #Hp⟩
    iexists Lr, Lw
    iframe Hp

theorem cacheFrom_absent (M : AuthMode) (n : Nat) (Mp : GMap GoString Loc) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (h : Mp !! user = none) :
    cacheFrom (GF := GF) M n Mp ⊢ cacheVerdictFrom M n user k e pt false := by
  cases M with
  | on γa =>
    unfold cacheFrom cacheVerdictFrom cacheOf
    iintro ⟨%i, %sta, #Hst, %Hn, %Hdom, -⟩
    iexists i, sta
    iframe Hst
    ipureintro; exact ⟨Hn, cacheVerdictP_absent sta Mp user k e pt Hdom h⟩
  | off => unfold cacheVerdictFrom; iintro -; itrivial
  | any => unfold cacheVerdictFrom; iintro -; itrivial

theorem entryFrom_verdict (M : AuthMode) (n : Nat) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (b : Bool) (Lr Lw : List adt.Entry)
    (hpt : pt = W32 0 ∨ pt = W32 1)
    (hb : k ≠ [] → (e = [] ∨ isOpenEnded e ∨ go.GoStringLt k e) →
      (b = true ↔ if e = [] then ∃ z ∈ (if pt = W32 0 then Lr else Lw), adt.inIvl z.1 k
        else ∀ x, adt.inIvl (queryIvl k e) x →
          ∃ z ∈ (if pt = W32 0 then Lr else Lw), adt.inIvl z.1 x)) :
    entryFrom (GF := GF) M n user Lr Lw ⊢ cacheVerdictFrom M n user k e pt b := by
  cases M with
  | on γa =>
    unfold entryFrom cacheVerdictFrom
    iintro ⟨%i, %sta, #Hst, %Hent⟩
    iexists i, sta
    iframe Hst
    ipureintro; exact ⟨Hent.1, cacheVerdictP_entry sta user k e pt b Lr Lw hpt Hent.2 hb⟩
  | off => unfold cacheVerdictFrom; iintro -; itrivial
  | any => unfold cacheVerdictFrom; iintro -; itrivial

end defs

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

set_option synthInstance.maxSize 512 in
/-- **The cache read under `rangePermCacheMu`, no older than the reader's lower bound** (the auth
plan's E3h): the guard's share of the cache's ghost variable at `(mp, j)` (the map the cache of the
state at `j`) agrees with the store's freshness's quarter, by which that state has the permissions
of a state at an index at least the published one, itself at least `n`: the map is that state's
cache too (`cacheOf_permView`). -/
theorem cacheFresh (st : Loc) (R : IProp GF) (M : AuthMode) (n : Nat) (q : Qp) (mp : GoMap)
    (Mp : GMap GoString Loc) :
    authInv (GF := GF) st R M ⊢ caGM M q mp Mp -∗ cacheOk M Mp -∗ authPubLbM M n ={⊤}=∗
      caGM M q mp Mp ∗ cacheFrom M n Mp := by
  cases M with
  | on γa =>
    iintro #Hinv Hg - #Hlb
    iunfold caGM at Hg
    icases Hg with ⟨%j, %sj, Hg, #Hsj, #Hof⟩
    iunfold authInv at Hinv
    icases Hinv with ⟨-, #Hrev, -⟩
    iinv Hrev with Hi Hclose
    iunfold revInv at Hi
    icases Hi with ⟨%r, Hr, Hv, Hc, >Hf⟩
    iunfold revFresh at Hf
    icases Hf with ⟨%p, Hp, #Hsp, Hrv, Hen, %v0, Hq0, %s, %j', %s', #Hs, #Hs', %Hpv⟩
    icombine Hg Hq0 gives %Hv0
    obtain ⟨-, Hv0⟩ := Hv0
    subst Hv0
    ihave %Hss := authStateAt_agree γa j sj s $$ [Hsj Hs]
    · iframe Hsj Hs
    subst Hss
    iunfold authPubLbM at Hlb
    ihave ⟨⟨Hp, -⟩, %Hle⟩ := ((and_intro (P := iprop(authPubAuth (GF := GF) γa p ∗ authPubLb γa n))
      .rfl (authPubAuth_lb_le γa p n)).trans persistent_and_sep_mp) $$ [Hp]
    · iframe Hp Hlb
    imod Hclose $$ [Hr Hv Hc Hp Hrv Hen Hq0] with -
    · inext
      iunfold revInv
      iexists r
      iframe Hr Hv Hc
      iunfold revFresh
      iexists p
      iframe Hp Hrv Hsp Hen
      iexists (mp, j)
      iframe Hq0
      iexists sj, j', s'
      iframe Hs Hs'
      ipureintro; exact Hpv
    imodintro
    isplitl [Hg]
    · iunfold caGM; iexists j, sj; iframe Hg Hsj Hof
    iunfold cacheFrom
    iexists j', s'
    iframe Hs'
    isplitr
    · ipureintro; omega
    iapply (cacheOf_permView sj s' Hpv.2 Mp) $$ Hof
  | off =>
    iintro - Hg #Hok -
    imodintro
    iframe Hg
    simp only [cacheOk, cacheFrom]
    iexact Hok
  | any =>
    iintro - Hg #Hok -
    imodintro
    iframe Hg
    simp only [cacheOk, cacheFrom]
    iexact Hok

end ghost

/-! ## The verdict lemmas, no older than `n` (as `VerdictLemmas.lean`'s) -/

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem permVerdictFrom_of_disabled (M : AuthMode) (n : Nat) (info : AuthInfo)
    (key rangeEnd : GoString) (op : PermType) :
    enabledVerdictFrom (GF := GF) M n false ⊢
      permVerdictFrom M n info key rangeEnd op GoInterface.nil := by
  cases M with
  | off => unfold permVerdictFrom; iintro -; ipureintro; rfl
  | any => unfold permVerdictFrom; iintro -; itrivial
  | on γa =>
    unfold enabledVerdictFrom permVerdictFrom
    iintro ⟨%i, %st, #Hst, %Hb⟩
    isplitr
    · iexists i, st; iframe #; ipureintro
      exact ⟨Hb.1, fun _ => by unfold permitted; left; exact Hb.2.symm⟩
    isplitr
    · iexists i, st; iframe #; ipureintro; exact ⟨Hb.1, fun _ => Or.inl Hb.2.symm⟩
    · iexists ⟨st, st, st, st⟩
      isplitr
      · iapply recordedVFrom_diag γa n i st Hb.1 $$ Hst
      · ipureintro; intro h; exact absurd rfl h

theorem permVerdictFrom_rev0 (M : AuthMode) (n : Nat) (info : AuthInfo) (key rangeEnd : GoString)
    (op : PermType) (err : GoInterface) (herr : err ≠ GoInterface.nil)
    (h0 : uint.nat info.Revision' = 0) :
    enabledVerdictFrom (GF := GF) M n true ⊢ permVerdictFrom M n info key rangeEnd op err := by
  cases M with
  | off => unfold enabledVerdictFrom; iintro %H; cases H
  | any => unfold permVerdictFrom; iintro -; itrivial
  | on γa =>
    unfold enabledVerdictFrom permVerdictFrom
    iintro ⟨%i, %st, #Hst, %Hb⟩
    isplitr
    · iexists i, st; iframe #; ipureintro; exact ⟨Hb.1, fun h => absurd h herr⟩
    isplitr
    · iexists i, st; iframe #; ipureintro; exact ⟨Hb.1, fun h => absurd h herr⟩
    · iexists ⟨st, st, st, st⟩
      isplitr
      · iapply recordedVFrom_diag γa n i st Hb.1 $$ Hst
      · ipureintro; intro _; unfold refusedV; exact ⟨Hb.2.symm, Or.inl h0⟩

theorem permVerdictFrom_oldRev (M : AuthMode) (n : Nat) (info : AuthInfo) (key rangeEnd : GoString)
    (op : PermType) (err : GoInterface) (cur : w64) (herr : err ≠ GoInterface.nil)
    (hlt : uint.nat info.Revision' < uint.nat cur) :
    enabledVerdictFrom (GF := GF) M n true ⊢ revisionVerdictFrom M n cur -∗
      permVerdictFrom M n info key rangeEnd op err := by
  cases M with
  | off => unfold enabledVerdictFrom; iintro %H -; cases H
  | any => unfold permVerdictFrom; iintro - -; itrivial
  | on γa =>
    unfold enabledVerdictFrom revisionVerdictFrom permVerdictFrom
    iintro ⟨%i, %sf, #Hsf, %Hb⟩ ⟨%j, %sr, #Hsr, %Hr⟩
    isplitr
    · iexists i, sf; iframe #; ipureintro; exact ⟨Hb.1, fun h => absurd h herr⟩
    isplitr
    · iexists i, sf; iframe #; ipureintro; exact ⟨Hb.1, fun h => absurd h herr⟩
    · iexists ⟨sf, sr, sf, sf⟩
      isplitr
      · iapply (recordedVFrom_intro γa n i j i i sf sr sf sf ⟨Hb.1, Hr.1, Hb.1, Hb.1⟩) $$ Hsf Hsr Hsf Hsf
      · ipureintro; intro _; unfold refusedV
        exact ⟨Hb.2.symm, Or.inr (Or.inl (Nat.lt_of_lt_of_eq hlt Hr.2))⟩

theorem permVerdictFrom_noUser (M : AuthMode) (n : Nat) (info : AuthInfo) (key rangeEnd : GoString)
    (op : PermType) (err : GoInterface) (sta : AuthState) (herr : err ≠ GoInterface.nil)
    (hu : sta.users !! info.Username' = none) :
    enabledVerdictFrom (GF := GF) M n true ⊢ authSnapFrom M n sta -∗
      permVerdictFrom M n info key rangeEnd op err := by
  cases M with
  | off => unfold enabledVerdictFrom; iintro %H -; cases H
  | any => unfold permVerdictFrom; iintro - -; itrivial
  | on γa =>
    unfold enabledVerdictFrom authSnapFrom permVerdictFrom
    iintro ⟨%i, %sf, #Hsf, %Hb⟩ ⟨%j, #Hsu, %Hj⟩
    isplitr
    · iexists i, sf; iframe #; ipureintro; exact ⟨Hb.1, fun h => absurd h herr⟩
    isplitr
    · iexists i, sf; iframe #; ipureintro; exact ⟨Hb.1, fun h => absurd h herr⟩
    · iexists ⟨sf, sf, sta, sf⟩
      isplitr
      · iapply (recordedVFrom_intro γa n i i j i sf sf sta sf ⟨Hb.1, Hb.1, Hj, Hb.1⟩) $$ Hsf Hsf Hsu Hsf
      · ipureintro; intro _; unfold refusedV
        refine ⟨Hb.2.symm, Or.inr (Or.inr fun u hu' => ?_)⟩
        have hu'' : sta.users !! info.Username' = some u := hu'
        rw [hu] at hu''; cases hu''

theorem permVerdictFrom_root (M : AuthMode) (n : Nat) (info : AuthInfo) (key rangeEnd : GoString)
    (op : PermType) (cur : w64) (sta : AuthState) (roles : User)
    (h0 : uint.nat info.Revision' ≠ 0) (hcur : uint.nat cur ≤ uint.nat info.Revision')
    (hu : sta.users !! info.Username' = some roles) (hroot : isRoot roles) :
    revisionVerdictFrom (GF := GF) M n cur ⊢ authSnapFrom M n sta -∗
      permVerdictFrom M n info key rangeEnd op GoInterface.nil := by
  cases M with
  | off => unfold permVerdictFrom; iintro - -; ipureintro; rfl
  | any => unfold permVerdictFrom; iintro - -; itrivial
  | on γa =>
    unfold revisionVerdictFrom authSnapFrom permVerdictFrom
    iintro ⟨%j, %sr, #Hsr, %Hr⟩ ⟨%i, #Hsu, %Hi⟩
    isplitr
    · iexists i, sta; iframe #; ipureintro
      exact ⟨Hi, fun _ => by unfold permitted granted; exact Or.inr ⟨h0, roles, hu, Or.inl hroot⟩⟩
    isplitr
    · iexists j, sr; iframe #; ipureintro
      exact ⟨Hr.1, fun _ => by right; rw [← Hr.2]; exact hcur⟩
    · iexists ⟨sta, sta, sta, sta⟩
      isplitr
      · iapply recordedVFrom_diag γa n i sta Hi $$ Hsu
      · ipureintro; intro h; exact absurd rfl h

theorem permVerdictFrom_cache_pass (M : AuthMode) (n : Nat) (info : AuthInfo)
    (key rangeEnd : GoString) (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (cur : w64)
    (sta : AuthState) (roles : User) (h0 : uint.nat info.Revision' ≠ 0)
    (hcur : uint.nat cur ≤ uint.nat info.Revision') (hu : sta.users !! info.Username' = some roles) :
    revisionVerdictFrom (GF := GF) M n cur ⊢ authSnapFrom M n sta -∗
      cacheVerdictFrom M n info.Username' key rangeEnd pt true -∗
      permVerdictFrom M n info key rangeEnd (permOp pt) GoInterface.nil := by
  cases M with
  | off => unfold permVerdictFrom; iintro - - -; ipureintro; rfl
  | any => unfold permVerdictFrom; iintro - - -; itrivial
  | on γa =>
    unfold revisionVerdictFrom authSnapFrom cacheVerdictFrom permVerdictFrom
    iintro ⟨%j, %sr, #Hsr, %Hr⟩ ⟨%i, #Hsu, %Hi⟩ ⟨%k, %sc, #Hsc, %Hc⟩
    ihave %Hk := authStateAt_permKeysOk γa k sc $$ Hsc
    isplitr
    · by_cases hs : reqShape key rangeEnd
      · iexists k, sc; iframe #; ipureintro
        refine ⟨Hc.1, fun _ => ?_⟩
        obtain ⟨roles', hu', hcov⟩ := (Hc.2 hs.1 hs.2 Hk).1 rfl
        unfold permitted granted
        exact Or.inr ⟨h0, roles', hu', Or.inr fun _ => hcov⟩
      · iexists i, sta; iframe #; ipureintro
        refine ⟨Hi, fun _ => ?_⟩
        unfold permitted granted
        exact Or.inr ⟨h0, roles, hu, Or.inr fun h => absurd h hs⟩
    isplitr
    · iexists j, sr; iframe #; ipureintro
      exact ⟨Hr.1, fun _ => by right; rw [← Hr.2]; exact hcur⟩
    · iexists ⟨sta, sta, sta, sta⟩
      isplitr
      · iapply recordedVFrom_diag γa n i sta Hi $$ Hsu
      · ipureintro; intro h; exact absurd rfl h

theorem permVerdictFrom_cache_refused (M : AuthMode) (n : Nat) (info : AuthInfo)
    (key rangeEnd : GoString) (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type)
    (err : GoInterface) (sta : AuthState) (roles : User) (herr : err ≠ GoInterface.nil)
    (hu : sta.users !! info.Username' = some roles) (hnroot : ¬ isRoot roles) :
    enabledVerdictFrom (GF := GF) M n true ⊢ authSnapFrom M n sta -∗
      cacheVerdictFrom M n info.Username' key rangeEnd pt false -∗
      permVerdictFrom M n info key rangeEnd (permOp pt) err := by
  cases M with
  | off => unfold enabledVerdictFrom; iintro %H - -; cases H
  | any => unfold permVerdictFrom; iintro - - -; itrivial
  | on γa =>
    unfold enabledVerdictFrom authSnapFrom cacheVerdictFrom permVerdictFrom
    iintro ⟨%i, %sf, #Hsf, %Hb⟩ ⟨%j, #Hsu, %Hj⟩ ⟨%k, %sc, #Hsc, %Hc⟩
    ihave %Hk := authStateAt_permKeysOk γa k sc $$ Hsc
    isplitr
    · iexists i, sf; iframe #; ipureintro; exact ⟨Hb.1, fun h => absurd h herr⟩
    isplitr
    · iexists i, sf; iframe #; ipureintro; exact ⟨Hb.1, fun h => absurd h herr⟩
    · iexists ⟨sf, sf, sta, sc⟩
      isplitr
      · iapply (recordedVFrom_intro γa n i i j k sf sf sta sc ⟨Hb.1, Hb.1, Hj, Hc.1⟩) $$ Hsf Hsf Hsu Hsc
      · ipureintro; intro _; unfold refusedV
        refine ⟨Hb.2.symm, Or.inr (Or.inr fun u hu' => ?_)⟩
        have hu'' : sta.users !! info.Username' = some u := hu'
        rw [hu] at hu''; cases hu''
        refine ⟨hnroot, fun hs u' hu2 hcov => ?_⟩
        have hu2' : sc.users !! info.Username' = some u' := hu2
        have hf := (Hc.2 hs.1 hs.2 Hk).2 ⟨u', hu2', hcov⟩
        cases hf

end lemmas

end auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

open auth

/-- **`as.isRangeOpPermitted(user, key, rangeEnd, pt)` read by a reader with the lower bound `n`**
(the auth plan's E3h): the verdict at a state no older than `n`. -/
def auth.authStore.isRangeOpPermitted.specLb : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) (user : GoString) (key re : GoSlice)
    (k e : GoString) (dk de : DFrac) (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      cacheRd st M ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜permTypOk pt⌝ ∗
      ⌜sint.Z key.len < 2 ^ 63 - 1⌝ ∗ authPubLbM M n }}
    (App (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"isRangeOpPermitted"))
      (Val #user)) (Val #key)) (Val #re)) (Val #pt))
  {{ (b : Bool), RET #b; cacheRd st M ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗
      cacheVerdictFrom M n user k e pt b }}

theorem auth.authStore.isRangeOpPermitted.wp_lb
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_checkKeyInterval : auth.checkKeyInterval.spec (GF := GF) (hG := hG))
    (h_checkKeyPoint : auth.checkKeyPoint.spec (GF := GF) (hG := hG)) :
    auth.authStore.isRangeOpPermitted.specLb (GF := GF) := by
  intro st R M n user key re k e dk de pt
  wp_start as ⟨#Hinv, Hrd, Hk, He, %Hpt, %Hlen, #Hlb⟩
  ihave #Hinv0 := Hinv
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  ihave %Hle := ownSlice_len _ _ _ $$ He
  have he0 := adt.slice_len_eq_zero Hle
  iunfold cacheRd at Hrd
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  iunfold cacheP at HP
  icases HP with ⟨%mp, %Mp, Hmp, HM, #Hall, HgM⟩
  imod (cacheFresh st R M n _ mp Mp) $$ Hinv0 HgM Hall Hlb with ⟨HgM, #Hfr⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 go.string _ mp Mp user $$ HM as HM
  cases HMu : Mp !! user with
  | none =>
    ihave #Hv := cacheFrom_absent M n Mp user k e pt HMu $$ Hfr
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
    wp_auto
    wp_apply h_String _ _ as %f -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Error
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hmp HM HgM] as Hrd
    · inext; iunfold cacheP; iexists mp, Mp; iframe Hmp HM Hall HgM
    iapply HΦ
    iunfold cacheRd
    iframe Hrd Hk He
    iexact Hv
  | some p =>
    ihave #Hent := cacheFrom_lookup M n Mp user p HMu $$ Hfr
    icases Hent with ⟨%Lr, %Lw, #Hp, #Hent⟩
    simp only [Option.isSome_some, _root_.decide_true, Bool.not_true, Option.getD_some]
    wp_auto
    wp_if_destruct
    · -- a point: `rangeEnd` empty
      rw [he0] at Hif
      wp_apply (h_checkKeyPoint lg p Lr Lw key k dk pt) $$ [$Hp $Hk] as %b ⟨Hk, %Hb⟩
      · ipureintro; exact ⟨Hpt, Hlen⟩
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hmp HM HgM] as Hrd
      · inext; iunfold cacheP; iexists mp, Mp; iframe Hmp HM Hall HgM
      iapply HΦ
      iunfold cacheRd
      iframe Hrd Hk He
      iapply (entryFrom_verdict M n user k e pt b Lr Lw Hpt) $$ Hent
      intro _ _
      rw [if_pos Hif]
      exact Hb
    · rw [he0] at Hif
      wp_apply (h_checkKeyInterval lg p Lr Lw key re k e dk de pt) $$ [$Hp $Hk $He]
        as %b ⟨Hk, He, %Hb⟩
      · ipureintro; exact Hpt
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hmp HM HgM] as Hrd
      · inext; iunfold cacheP; iexists mp, Mp; iframe Hmp HM Hall HgM
      iapply HΦ
      iunfold cacheRd
      iframe Hrd Hk He
      iapply (entryFrom_verdict M n user k e pt b Lr Lw Hpt) $$ Hent
      intro hk hr
      rw [if_neg Hif]
      rcases hr with h | h
      · exact absurd h Hif
      · exact Hb hk h

/-- **`as.isOpPermitted(...)` read by a reader with the lower bound `n`** (the auth plan's E3h): the
verdict at states no older than `n` (`permVerdictFrom`). -/
def auth.authStore.isOpPermitted.specLb : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) (info : AuthInfo) (key re : GoSlice)
    (k e : List w8) (dk de : DFrac) (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ authRd st R M ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜permTypOk pt⌝ ∗
      ⌜sint.Z key.len < 2 ^ 63 - 1⌝ ∗ authPubLbM M n }}
    (App (App (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"isOpPermitted")) (Val #info.Username')) (Val #info.Revision')) (Val #key)) (Val #re))
      (Val #pt))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ authErrIs err ∗
      permVerdictFrom M n info k e (permOp pt) err }}

theorem auth.authStore.isOpPermitted.wp_lb
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.specLb (GF := GF))
    (h_Revision : auth.authStore.Revision.specLb (GF := GF))
    (h_Uint64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (h_ByteString : zap.ByteString.spec (GF := GF) (hG := hG))
    (h_ZError : zap.Error.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_hasRootRole : auth.hasRootRole.spec (GF := GF) (hG := hG))
    (h_lockedReadTx : auth.authStore.lockedReadTx.specLb (GF := GF) (hG := hG))
    (h_isRangeOpPermitted : auth.authStore.isRangeOpPermitted.specLb (GF := GF)) :
    auth.authStore.isOpPermitted.specLb (GF := GF) := by
  intro st R M n info key re k e dk de pt
  wp_start as ⟨#Hinv, Hrd, Hk, He, %Hpt, %Hlen, #Hlb⟩
  iunfold authRd at Hrd
  icases Hrd with ⟨Hen, Hca, Hbr, HR⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨#HeUE, #HeUNF, #HePD, #HeOR, #HeIT, -, -⟩
  ihave #HeUE' := HeUE
  iunfold authErrVar at HeUE'
  icases HeUE' with ⟨%eUE, #HeUEa, -⟩
  ihave #HePD' := HePD
  iunfold authErrVar at HePD'
  icases HePD' with ⟨%ePD, #HePDa, -⟩
  ihave #HeOR' := HeOR
  iunfold authErrVar at HeOR'
  icases HeOR' with ⟨%eOR, #HeORa, -⟩
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (h_IsAuthEnabled st R M n) $$ [$Hinv $Hen $Hlb] as %en ⟨Hen, #Hev⟩
  cases en
  · wp_auto
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs; ileft; ipureintro; rfl
    · iapply permVerdictFrom_of_disabled M n info k e (permOp pt) $$ Hev
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs
      iright
      iexists ErrUserEmpty, eUE
      iframe HeUEa
      ipureintro; simp
    · iapply (permVerdictFrom_rev0 M n info k e (permOp pt) (GoInterface.ok eUE) (fun h => by cases h)
        (by rw [Hif]; word)) $$ Hev
  have h0 : uint.nat info.Revision' ≠ 0 := fun h => Hif (by word)
  wp_apply (h_Revision st R M n) $$ [$Hinv $Hlb] as %cur #Hrv
  (try wp_auto)
  wp_if_destruct
  · wp_apply h_Uint64 _ _ as %f1 -
    wp_apply h_Uint64 _ _ as %f2 -
    wp_apply h_ByteString _ _ as %f3 -
    (try wp_auto)
    wp_apply h_ZError _ as %f4 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3, f4]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Warn
    · ipureintro; exact Hlgnn
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs
      iright
      iexists ErrAuthOldRevision, eOR
      iframe HeORa
      ipureintro; simp
    · iapply (permVerdictFrom_oldRev M n info k e (permOp pt) (GoInterface.ok eOR) cur
        (fun h => by cases h) (by word)) $$ Hev Hrv
  have hcur : uint.nat cur ≤ uint.nat info.Revision' := by word
  wp_apply (h_lockedReadTx st R M n) $$ [$Hinv $Hbr $HR $Hlb] as %tx ⟨Hbr, Htx⟩
  iunfold authReadTxLockedFrom at Htx
  icases Htx with ⟨%ti, %Hti, Htx⟩
  subst Hti
  icases Htx with ⟨%sta, %Hs, Htok, #Hsnap, #Hreads⟩
  iunfold authTxReads at Hreads
  icases Hreads with ⟨#Hrds, #HRU⟩
  iunfold authReaderOk at Hrds
  icases Hrds with ⟨#HUG, -, -, -, -⟩
  wp_auto
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #info.Username'))
  iapply HUG $$ Htok
  inext
  iintro %u ⟨Htok, Hu⟩
  wp_auto
  wp_if_destruct
  · ihave %Hnone := userOut_null sta info.Username' $$ Hu
    wp_apply h_String _ _ as %f -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Error
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
    iapply HRU $$ Htok
    inext
    iintro HR
    (try wp_auto)
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs
      iright
      iexists ErrPermissionDenied, ePD
      iframe HePDa
      ipureintro; simp
    · iapply (permVerdictFrom_noUser M n info k e (permOp pt) (GoInterface.ok ePD) sta
        (fun h => by cases h) Hnone) $$ Hev Hsnap
  ihave Hu' := userOut_some u sta info.Username' Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  wp_apply h_hasRootRole $$ [$Hu] as %root ⟨Hu, %Hroot⟩
  · ipureintro; rw [Hur.2.1]; exact Hur.2.2
  cases root
  · have hn : ¬ isRoot roles := by rw [← Hur.2.1]; exact of_decide_eq_false Hroot.symm
    (try wp_auto)
    wp_apply (h_isRangeOpPermitted st R M n info.Username' key re k e dk de pt) $$ [$Hinv $Hca $Hk $He $Hlb]
      as %okr ⟨Hca, Hk, He, #Hcv⟩
    · ipureintro; exact ⟨Hpt, Hlen⟩
    cases okr
    · (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iunfold authRd
      iframe
      isplitl []
      · iunfold authErrIs
        iright
        iexists ErrPermissionDenied, ePD
        iframe HePDa
        ipureintro; simp
      · iapply (permVerdictFrom_cache_refused M n info k e pt (GoInterface.ok ePD) sta roles
          (fun h => by cases h) Hur.1 hn) $$ Hev Hsnap Hcv
    · (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iunfold authRd
      iframe
      isplitl []
      · iunfold authErrIs; ileft; ipureintro; rfl
      · iapply (permVerdictFrom_cache_pass M n info k e pt cur sta roles h0 hcur Hur.1) $$ Hrv Hsnap Hcv
  · have hroot : isRoot roles := by rw [← Hur.2.1]; exact of_decide_eq_true Hroot.symm
    (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
    iapply HRU $$ Htok
    inext
    iintro HR
    (try wp_auto)
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs; ileft; ipureintro; rfl
    · iapply (permVerdictFrom_root M n info k e (permOp pt) cur sta roles h0 hcur Hur.1 hroot) $$ Hrv Hsnap

end proof

end EtcdGrove
end Perennial
