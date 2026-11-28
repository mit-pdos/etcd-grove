/-
**The apply package's auth-store checks at the latest state** (the auth plan's E2s, 2026-10-26;
`notes/decisions.md`, "E2s of the auth plan"). `isAuthStore`'s checks (`permCheck2`, `permCheck3`,
`IsAdminPermitted`) give their verdicts at some recorded state per read (S3), all a concurrent
caller can be promised. The apply thread holds the admin side's authority between its batch
transactions (`auth.latestRes`, E2r/E2s), so its checks can be promised the latest state's
(`auth.permVerdictL`, `auth.adminVerdictL`): `isAuthStoreL st RD M L` states them over a resource
family `L hs` the caller holds and gets back, and the real store meets it with
`L := auth.latestRes st M` (`isAuthStoreL_of_authInv`).

The pure part: one permission's verdict at the latest state in `kvGranted`'s form
(`granted1`, E2q's `etcdserver/KVAuthModel.lean`), from a check's (`verdictL_one`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass
public import Proof.go_etcd_io.etcd.server.v3.auth.LatestAdmin

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3 go_etcd_io.etcd.api.v3

/-! ## The verdicts at the latest state (pure) -/

section pure
variable [GooseExts]

/-- **`P` of the latest state** of the history `hs` in the mode `M`: in `on γa`, `P` holds of the
last state of `hs`; in the other modes nothing is said. -/
def latestOk (M : auth.AuthMode) (hs : List auth.AuthState) (P : auth.AuthState → Prop) : Prop :=
  match M with
  | .on _ => ∀ stl, hs.getLast? = some stl → P stl
  | _ => True

theorem latestOk_mono (M : auth.AuthMode) (hs : List auth.AuthState) (P Q : auth.AuthState → Prop)
    (h : ∀ stl, P stl → Q stl) (hp : latestOk M hs P) : latestOk M hs Q := by
  cases M with
  | on γa => intro stl hl; exact h stl (hp stl hl)
  | off => trivial
  | any => trivial

theorem latestOk_and (M : auth.AuthMode) (hs : List auth.AuthState) (P Q : auth.AuthState → Prop)
    (hp : latestOk M hs P) (hq : latestOk M hs Q) : latestOk M hs (fun s => P s ∧ Q s) := by
  cases M with
  | on γa => intro stl hl; exact ⟨hp stl hl, hq stl hl⟩
  | off => trivial
  | any => trivial

/-- **One permission granted at the state `stl`** to the principal `ai` (`kvGranted`'s form for
one permission, `etcdserver/KVAuthModel.lean`): auth disabled, or the principal's revision not `0`
and not below the store's, and its user existing with the root role or covering the permission. -/
def granted1 (stl : auth.AuthState) (ai : auth.AuthInfoM) (x : Perm3) : Prop :=
  stl.enabled = false ∨ (ai.rev ≠ 0 ∧ stl.revision ≤ ai.rev ∧
    ∃ u, stl.users !! ai.user = some u ∧ (auth.isRoot u ∨ auth.covers stl u x.2.2 x.1 x.2.1))

/-- **The checks of `perms` all passed at the latest state**. -/
def passedL (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (perms : List Perm3) : Prop :=
  latestOk M hs (fun stl => ∀ x ∈ perms, granted1 stl ai x)

/-- **One of the checks of `perms` refused at the latest state**. -/
def refusedL (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (perms : List Perm3) : Prop :=
  latestOk M hs (fun stl => ∃ x ∈ perms, ¬ granted1 stl ai x)

/-- **The permissions are of the cache's shape whenever auth is enabled** at the latest state (the
model's `kvDet`): what makes a check's verdict exact. -/
def shapedL (M : auth.AuthMode) (hs : List auth.AuthState) (perms : List Perm3) : Prop :=
  latestOk M hs (fun stl => stl.enabled = true → ∀ x ∈ perms, auth.reqShape x.1 x.2.1)

theorem passedL_nil (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM) :
    passedL M hs ai [] := by
  cases M with
  | on γa => intro stl _ x hx; cases hx
  | off => trivial
  | any => trivial

theorem passedL_append (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (l1 l2 : List Perm3) (h1 : passedL M hs ai l1) (h2 : passedL M hs ai l2) :
    passedL M hs ai (l1 ++ l2) := by
  cases M with
  | on γa =>
    intro stl hl x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact h1 stl hl x hx
    · exact h2 stl hl x hx
  | off => trivial
  | any => trivial

theorem refusedL_append_right (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (l1 l2 : List Perm3) (h : refusedL M hs ai l2) : refusedL M hs ai (l1 ++ l2) := by
  cases M with
  | on γa =>
    intro stl hl
    obtain ⟨x, hx, hn⟩ := h stl hl
    exact ⟨x, List.mem_append_right l1 hx, hn⟩
  | off => trivial
  | any => trivial

theorem refusedL_append_left (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (l1 l2 : List Perm3) (h : refusedL M hs ai l1) : refusedL M hs ai (l1 ++ l2) := by
  cases M with
  | on γa =>
    intro stl hl
    obtain ⟨x, hx, hn⟩ := h stl hl
    exact ⟨x, List.mem_append_left l2 hx, hn⟩
  | off => trivial
  | any => trivial

theorem shapedL_append (M : auth.AuthMode) (hs : List auth.AuthState) (l1 l2 : List Perm3) :
    shapedL M hs (l1 ++ l2) ↔ shapedL M hs l1 ∧ shapedL M hs l2 := by
  cases M with
  | on γa =>
    constructor
    · intro h
      exact ⟨fun stl hl he x hx => h stl hl he x (List.mem_append_left l2 hx),
        fun stl hl he x hx => h stl hl he x (List.mem_append_right l1 hx)⟩
    · rintro ⟨h1, h2⟩ stl hl he x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h1 stl hl he x hx
      · exact h2 stl hl he x hx
  | off => exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  | any => exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩

/-- **One check's latest verdict, in `granted1`'s form**: for a permission of the cache's shape
whenever auth is enabled, a pass is the permission granted at the latest state and a refusal its
negation. -/
theorem verdictL_one (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (k e : GoString) (op : auth.PermType) (err : GoInterface)
    (hv : auth.permVerdictL M hs ai k e op err) (hsh : shapedL M hs [(k, e, op)]) :
    (err = GoInterface.nil → passedL M hs ai [(k, e, op)]) ∧
      (err ≠ GoInterface.nil → refusedL M hs ai [(k, e, op)]) := by
  cases M with
  | on γa =>
    constructor
    · intro herr stl hl x hx
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨hp, -⟩ := hv stl hl
      obtain ⟨hpm, hrev⟩ := hp herr
      unfold granted1
      by_cases hen : stl.enabled = false
      · exact Or.inl hen
      · have hen' : stl.enabled = true := by simpa using hen
        have hs1 := hsh stl hl hen' (k, e, op) (List.mem_singleton.2 rfl)
        have := (auth.permVerdictL_granted γa hs ai k e op err stl hl hs1 hv).1 herr
        exact this
    · intro herr stl hl
      refine ⟨(k, e, op), List.mem_singleton.2 rfl, ?_⟩
      obtain ⟨-, hr, -⟩ := hv stl hl
      have hrv := hr herr
      have hen : stl.enabled = true := hrv.1
      have hs1 := hsh stl hl hen (k, e, op) (List.mem_singleton.2 rfl)
      intro hg
      exact herr ((auth.permVerdictL_granted γa hs ai k e op err stl hl hs1 hv).2 hg)
  | off => exact ⟨fun _ => trivial, fun _ => trivial⟩
  | any => exact ⟨fun _ => trivial, fun _ => trivial⟩

/-! ### The lease part of a check at the latest state (auth-lease S2, `notes/auth-lease-s2-draft.md`) -/

/-- **The lease check passed at the latest state** (`checkLeasePuts` of the lease `id` at the owner's item
map `I`): an admin there (`IsAdminPermitted`: no revision check, `store.go:915-936`), or every key `I`
attaches to `id` write-granted there (`isOpPermitted`'s `granted1`). -/
def leasePassedL (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64) : Prop :=
  latestOk M hs (fun stl => auth.adminOk stl (some ai) ∨
    ∀ k : GoString, I.lookup ⟨k⟩ = some id → granted1 stl ai (k, [], .write))

/-- **The lease check refused at the latest state**: not an admin there, and a key of `id` not
write-granted there (`refusedL`'s form: `¬ leasePassedL` is not what a refusal gives, `latestOk` being
vacuous at an empty history and in the mode `any`). -/
def leaseRefusedL (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64) : Prop :=
  latestOk M hs (fun stl => ¬ auth.adminOk stl (some ai) ∧
    ∃ k : GoString, I.lookup ⟨k⟩ = some id ∧ ¬ granted1 stl ai (k, [], .write))

/-- **The lease's keys are of the cache's shape whenever auth is enabled** at the latest state (what
makes each key's check exact). -/
def leaseShapedL (M : auth.AuthMode) (hs : List auth.AuthState)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64) : Prop :=
  latestOk M hs (fun stl => stl.enabled = true →
    ∀ k : GoString, I.lookup ⟨k⟩ = some id → auth.reqShape k [])

/-- A lease attaching no key passes (whatever the principal). -/
theorem leasePassedL_of_none (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64)
    (h : ∀ k : GoString, I.lookup ⟨k⟩ ≠ some id) : leasePassedL M hs ai I id := by
  cases M with
  | on γa => intro stl _; right; intro k hk; exact absurd hk (h k)
  | off => trivial
  | any => trivial

/-- A lease attaching no key is not refused, so a refusal of it gives anything. -/
theorem leaseRefusedL_none_false (γa : auth.AuthNames) (hs : List auth.AuthState) (stl : auth.AuthState)
    (hl : hs.getLast? = some stl) (ai : auth.AuthInfoM)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64)
    (h : ∀ k : GoString, I.lookup ⟨k⟩ ≠ some id) (hr : leaseRefusedL (.on γa) hs ai I id) : False := by
  obtain ⟨-, k, hk, -⟩ := hr stl hl
  exact h k hk

/-- A lease attaching no key is of the shape. -/
theorem leaseShapedL_of_none (M : auth.AuthMode) (hs : List auth.AuthState)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64)
    (h : ∀ k : GoString, I.lookup ⟨k⟩ ≠ some id) : leaseShapedL M hs I id := by
  cases M with
  | on γa => intro stl _ _ k hk; exact absurd hk (h k)
  | off => trivial
  | any => trivial

end pure

/-! ## The contracts -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `permCheck2` at the latest state: with the caller's latest-state resource `L hs` (held and
given back), the verdict of the latest state of `hs` (`auth.permVerdictL`). -/
def permCheck2L (ai : GoInterfaceOk) (m : GoString) (RD : IProp GF) (M : auth.AuthMode)
    (L : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(□ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac) (key : GoSlice) (k : List w8)
      (dk : DFrac) (hs : List auth.AuthState),
    {{ a ↦{dq} info ∗ key ↦*{dk} k ∗ RD ∗ L hs ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
      (App (App (Val #(methods ai.ty m ai.v)) (Val #a)) (Val #key))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ RD ∗ L hs ∗ authApplyErrIs err ∗
        ⌜auth.permVerdictL M hs (auth.authInfoM info) k [] .write err⌝ ∗
        auth.permVerdict M info k [] .write err }}))

/-- `permCheck3` at the latest state (as `permCheck2L`). -/
def permCheck3L (ai : GoInterfaceOk) (m : GoString) (RD : IProp GF) (M : auth.AuthMode)
    (op : auth.PermType) (L : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(□ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac) (key re : GoSlice) (k e : List w8)
      (dk de : DFrac) (hs : List auth.AuthState),
    {{ a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ RD ∗ L hs ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
      (App (App (App (Val #(methods ai.ty m ai.v)) (Val #a)) (Val #key)) (Val #re))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ RD ∗ L hs ∗
        authApplyErrIs err ∗ ⌜auth.permVerdictL M hs (auth.authInfoM info) k e op err⌝ ∗
        auth.permVerdict M info k e op err }}))

/-- **The auth store's checks at the latest state** (see the file header): the three permission
checks and `IsAdminPermitted` (on a message), with the caller's resource family `L` (the apply
thread's: `auth.latestRes st M`); (auth-lease S2) the latest state recorded from `L hs`
(`auth.latestSnap`), which a passed admin check's class needs (`leaseKeysClass`). -/
def isAuthStoreL (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode)
    (L : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    permCheck2L ai go!"IsPutPermitted" RD M L ∗
    permCheck3L ai go!"IsRangePermitted" RD M .read L ∗
    permCheck3L ai go!"IsDeleteRangePermitted" RD M .write L ∗
    □ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac) (hs : List auth.AuthState),
      {{ a ↦{dq} info ∗ RD ∗ L hs }} (App (Val #(methods ai.ty go!"IsAdminPermitted" ai.v)) (Val #a))
      {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ RD ∗ L hs ∗ authApplyErrIs err ∗
          ⌜auth.adminVerdictL M hs (some (auth.authInfoM info)) err⌝ }}) ∗
    □ (∀ hs : List auth.AuthState, L hs -∗ L hs ∗ auth.latestSnap M hs))

instance isAuthStoreL_persistent (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode)
    (L : List auth.AuthState → IProp GF) : Persistent (isAuthStoreL st RD M L) := by
  unfold isAuthStoreL permCheck2L permCheck3L; infer_instance

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The real store's checks at the latest state** (`auth/Latest.lean`, `auth/LatestAdmin.lean`),
with the reader resource `auth.authRd st R M` and the apply thread's `auth.latestResC st M γc` (its
write token on the backend names `γc`). -/
theorem isAuthStoreL_of_authInv
    (hPut : auth.authStore.IsPutPermitted.specL (GF := GF) (hG := hG))
    (hRange : auth.authStore.IsRangePermitted.specL (GF := GF) (hG := hG))
    (hDel : auth.authStore.IsDeleteRangePermitted.specL (GF := GF) (hG := hG))
    (hAdmin : auth.authStore.IsAdminPermitted.specL (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : auth.AuthMode) (γc : auth.AuthBkNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      isAuthStoreL (auth.authIface st) (auth.authRd st R M) M (auth.latestResC st M γc) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold isAuthStoreL
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  isplitr
  · iunfold permCheck2L
    iintro !> %a %info %dq %key %k %dk %hs %Φ !> ⟨Ha, Hk, Hrd, HL, %Hlen⟩ HΦ
    iunfold auth.latestResC at HL
    icases HL with ⟨HL, Hw⟩
    iunfold auth.latestRes at HL
    icases HL with ⟨Hown, %b, %sc, Hfl, Hca, #Hev, #Hsn, %Htie⟩
    ihave ⟨Hown, #Hsnap⟩ := auth.authOwn_latestSnap M hs $$ Hown
    iapply (hPut st R M hs γc b sc a info dq key k dk) $$ [Ha Hk Hrd Hown Hw Hfl Hca]
    · iframe; iframe #; ipureintro; exact ⟨Hlen, Htie⟩
    iintro !> %err ⟨Hrd, Ha, Hk, #Herr, Hown, Hw, Hfl, Hca, %Hv⟩
    iapply HΦ
    iframe
    isplitl [Hown Hw Hfl Hca]
    · iunfold auth.latestResC; iframe Hw; iunfold auth.latestRes; iframe Hown; iexists b, sc; iframe Hfl Hca Hev Hsn; ipureintro; exact Htie
    isplitl []
    · iapply authErrIs_authApplyErrIs err $$ [$Hpkg $Herr]
    isplitl []
    · ipureintro; exact Hv
    · iapply (auth.permVerdict_of_L M hs info _ _ _ err Hv) $$ Hsnap
  isplitr
  · iunfold permCheck3L
    iintro !> %a %info %dq %key %re %k %e %dk %de %hs %Φ !> ⟨Ha, Hk, He, Hrd, HL, %Hlen⟩ HΦ
    iunfold auth.latestResC at HL
    icases HL with ⟨HL, Hw⟩
    iunfold auth.latestRes at HL
    icases HL with ⟨Hown, %b, %sc, Hfl, Hca, #Hev, #Hsn, %Htie⟩
    ihave ⟨Hown, #Hsnap⟩ := auth.authOwn_latestSnap M hs $$ Hown
    iapply (hRange st R M hs γc b sc a info dq key re k e dk de) $$ [Ha Hk He Hrd Hown Hw Hfl Hca]
    · iframe; iframe #; ipureintro; exact ⟨Hlen, Htie⟩
    iintro !> %err ⟨Hrd, Ha, Hk, He, #Herr, Hown, Hw, Hfl, Hca, %Hv⟩
    iapply HΦ
    iframe
    isplitl [Hown Hw Hfl Hca]
    · iunfold auth.latestResC; iframe Hw; iunfold auth.latestRes; iframe Hown; iexists b, sc; iframe Hfl Hca Hev Hsn; ipureintro; exact Htie
    isplitl []
    · iapply authErrIs_authApplyErrIs err $$ [$Hpkg $Herr]
    isplitl []
    · ipureintro; exact Hv
    · iapply (auth.permVerdict_of_L M hs info _ _ _ err Hv) $$ Hsnap
  isplitr
  · iunfold permCheck3L
    iintro !> %a %info %dq %key %re %k %e %dk %de %hs %Φ !> ⟨Ha, Hk, He, Hrd, HL, %Hlen⟩ HΦ
    iunfold auth.latestResC at HL
    icases HL with ⟨HL, Hw⟩
    iunfold auth.latestRes at HL
    icases HL with ⟨Hown, %b, %sc, Hfl, Hca, #Hev, #Hsn, %Htie⟩
    ihave ⟨Hown, #Hsnap⟩ := auth.authOwn_latestSnap M hs $$ Hown
    iapply (hDel st R M hs γc b sc a info dq key re k e dk de) $$ [Ha Hk He Hrd Hown Hw Hfl Hca]
    · iframe; iframe #; ipureintro; exact ⟨Hlen, Htie⟩
    iintro !> %err ⟨Hrd, Ha, Hk, He, #Herr, Hown, Hw, Hfl, Hca, %Hv⟩
    iapply HΦ
    iframe
    isplitl [Hown Hw Hfl Hca]
    · iunfold auth.latestResC; iframe Hw; iunfold auth.latestRes; iframe Hown; iexists b, sc; iframe Hfl Hca Hev Hsn; ipureintro; exact Htie
    isplitl []
    · iapply authErrIs_authApplyErrIs err $$ [$Hpkg $Herr]
    isplitl []
    · ipureintro; exact Hv
    · iapply (auth.permVerdict_of_L M hs info _ _ _ err Hv) $$ Hsnap
  isplitr
  rotate_left
  · iintro !> %hs HL
    iunfold auth.latestResC at HL
    icases HL with ⟨HL, Hw⟩
    iunfold auth.latestRes at HL
    icases HL with ⟨Hown, %b, %sc, Hfl, Hca, #Hev, #Hsn, %Htie⟩
    ihave ⟨Hown, #Hsnap⟩ := auth.authOwn_latestSnap M hs $$ Hown
    iframe Hsnap
    iunfold auth.latestResC; iframe Hw; iunfold auth.latestRes; iframe Hown
    iexists b, sc; iframe Hfl Hca Hev Hsn; ipureintro; exact Htie
  iintro !> %a %info %dq %hs %Φ !> ⟨Ha, Hrd, HL⟩ HΦ
  iunfold auth.latestResC at HL
  icases HL with ⟨HL, Hw⟩
  iunfold auth.latestRes at HL
  icases HL with ⟨Hown, %b, %sc, Hfl, Hca, #Hev, #Hsn, %Htie⟩
  ihave Ha' : auth.authInfoAt a dq (some info) $$ [Ha]
  · iunfold auth.authInfoAt; iexact Ha
  iapply (hAdmin st R M hs γc b sc a (some info) dq) $$ [Ha' Hrd Hown Hw Hfl]
  · iframe; iframe #; ipureintro; exact Htie
  iintro !> %err ⟨Hrd, Ha', #Herr, Hown, Hw, Hfl, %Hv⟩
  iunfold auth.authInfoAt at Ha'
  iapply HΦ
  iframe
  isplitl [Hown Hw Hfl Hca]
  · iunfold auth.latestResC; iframe Hw; iunfold auth.latestRes; iframe Hown; iexists b, sc; iframe Hfl Hca Hev Hsn; ipureintro; exact Htie
  isplitl []
  · iapply authErrIs_authApplyErrIs err $$ [$Hpkg $Herr]
  · ipureintro; exact Hv

end proof

end apply
end EtcdGrove
end Perennial
