/-
**The simple token provider meets the token provider's contract** (`tokenSimple`,
`simple_token.go`; the auth plan's S5b, 2026-10-24; `notes/decisions.md`, "S5b of the auth
plan"). Lean-first (no Rocq counterpart).

`tokenSimple` (etcd's default provider) keeps a map `simpleTokens` from token to user name under
`simpleTokensMu`, and a TTL keeper (`simpleTokenTTLKeeper`, while auth is enabled) whose goroutine
deletes expired tokens. The binding (`tokenProviderOk`'s `info` clause): every token in the map was
issued to its user. The lock invariant (`simpleLk`) holds, for every entry `t ↦ u` of the map, the
persistent `tokIssued`-element `(t, u)` and the right to issue `t` (`tokFresh`, exclusive), so that
`assign`'s caller, who holds the right to issue its token (`authnCtx`), knows the token is not in
the map: `assignSimpleTokenToUser`'s panic on a token issued twice is unreachable.

**Three hypotheses, not axioms** (`tokenSimple_ok`'s premises): the functions Perennial cannot
reach. `isValidSimpleToken` parses the token's index with `strconv.ParseUint` (Perennial does not
translate `strconv`) and waits on the raft index or the context; it is assumed to return
(`ValidSpec`). The keeper's `run` (a `time.Ticker`, `Time.After`) and `stop` (the channel protocol
between them) are assumed to return given the keeper's resources (`keeperOk`: its read-only fields,
the provider's mutex with its invariant, the delete callback's spec, the two channels in
invariants), which the proof of `enable` produces. `ValidSpec` quantifies over every context: the
Go function calls `ctx.Done()`, so it holds of contexts; the contract's `info` clause has no
context premise (`InvAuth` is generic over later credits, Perennial's contexts are not), which is
where the gap is.

**The mode**: the provider is created with the names of the issued tokens and of the fresh tokens
(`γt`, `γf`), before the store's history exists; it meets the contract in the mode `on γa` for the
history allocated with those names (`authHist_alloc`). In `off` and `any` the contract's `assign`
premise carries no right to issue the token, which the panic's refutation needs.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Perennial.Golang.Theory.Chan.AuSpec.ChanAuNew
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.String
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

namespace auth

section defs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&t.<f>` (a `*tokenSimple`) -/
abbrev tsF (f : GoString) (p : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.auth.tokenSimple f p

/-- `&tm.<f>` (a `*simpleTokenTTLKeeper`) -/
abbrev kpF (f : GoString) (k : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper f k

end defs

section pred
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A keeper's map (`tm.tokens`, its expiry times) and its TTL, read under the provider's mutex:
the lock invariant holds them for every keeper the provider created (an old keeper's goroutine may
still take the lock after `disable()` replaced it). -/
def keeperMap (k : Loc) : IProp GF :=
  iprop(∃ (km : Loc) (tm : GMap GoString time.Time) (ttl : time.Duration),
    kpF go!"tokens" k ↦□ km ∗ km ↦$ tm ∗ kpF go!"simpleTokenTTL" k ↦□ ttl)

/-- **What `simpleTokensMu` guards** (the provider `p`, the issued tokens' names `γt`, the fresh
tokens' `γf`): the map `simpleTokens` with, for each entry `t ↦ u`, the persistent issued element
`(t, u)` and the right to issue `t`; the issued tokens' authority; the current keeper (`nil`, or one
of the keepers created, `ks`, whose maps it holds); the TTL (positive: `enable` then never reads
the package default). -/
def simpleLk (p : Loc) (γt γf : GName) : IProp GF :=
  iprop(∃ (mp : Loc) (m : GMap GoString GoString) (k : Loc) (ks : List Loc) (ttl : time.Duration)
      (S : GMap (GoString × GoString) Unit),
    tsF go!"simpleTokens" p ↦ mp ∗ mp ↦$ m ∗
    ([∗map] t ↦ u ∈ m, ghostMapElem γt (t, u) DFrac.discard () ∗ ghostMapElem γf t (DFrac.own 1) ()) ∗
    tokAuth γt S ∗
    tsF go!"simpleTokenKeeper" p ↦ k ∗ ⌜k = null ∨ k ∈ ks⌝ ∗ ([∗list] k' ∈ ks, keeperMap k') ∗
    tsF go!"simpleTokenTTL" p ↦ ttl ∗ ⌜0 < sint.Z ttl⌝)

/-- The provider's read-only fields and its mutex (persistent). -/
def simpleOk (p : Loc) (γt γf : GName) : IProp GF :=
  iprop(∃ (lg : Loc), tsF go!"lg" p ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    sync.isMutex (tsF go!"simpleTokensMu" p) (simpleLk p γt γf))

instance simpleOk_persistent (p : Loc) (γt γf : GName) :
    Persistent (simpleOk (GF := GF) p γt γf) := by
  unfold simpleOk; infer_instance

end pred

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- A keeper of the list, its map out and back. -/
theorem keepers_acc (ks : List Loc) (k : Loc) (hk : k ∈ ks) :
    ([∗list] k' ∈ ks, keeperMap (GF := GF) k') ⊢
      keeperMap k ∗ (keeperMap k -∗ [∗list] k' ∈ ks, keeperMap k') := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
  refine (BigSepL.bigSepL_lookup_acc (Φ := fun _ x => keeperMap (GF := GF) x) hi).1.trans
    (sep_mono_right ?_)
  iintro H Hk
  have hset : ks.set i k = ks := by
    apply List.ext_getElem?; intro j
    rw [List.getElem?_set]; split
    · next h => subst h; obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp hi; simp [h1, h2]
    · rfl
  ihave H' := H $$ %k Hk
  rw [hset]; iexact H'

/-- The issued element of a token the map holds (persistent), the map's resources kept. -/
theorem big_issued (γt γf : GName) (m : GMap GoString GoString) (t : GoString) :
    ([∗map] t ↦ u ∈ m, iprop(ghostMapElem (GF := GF) γt (t, u) DFrac.discard () ∗
        ghostMapElem γf t (DFrac.own 1) ())) ⊢
      ([∗map] t ↦ u ∈ m, iprop(ghostMapElem (GF := GF) γt (t, u) DFrac.discard () ∗
        ghostMapElem γf t (DFrac.own 1) ())) ∗
      □ (∀ u : GoString, ⌜m !! t = some u⌝ → ghostMapElem γt (t, u) DFrac.discard ()) := by
  cases h : m !! t with
  | none =>
    iintro H; iframe H
    iintro !> %u %hu
    exact absurd hu (by simp)
  | some u0 =>
    iintro H
    icases (BigSepM.bigSepM_lookup_acc h).1 $$ H with ⟨⟨#Hi, Hf⟩, Hback⟩
    ihave H := Hback $$ [Hf]
    · iframe Hf Hi
    iframe H
    iintro !> %u %hu
    simp only [Option.some.injEq] at hu
    subst hu; iexact Hi

/-- `tm.resetSimpleToken(token)`: the keeper's map, kept. -/
theorem keeper_reset (k : Loc) (token : GoString) :
    {{ keeperMap (GF := GF) k }}
      (App (Val #(methods (go.GoType.PointerType simpleTokenTTLKeeper.ty) go!"resetSimpleToken" #k))
        (Val #token))
    {{ RET #(); keeperMap k }} := by
  wp_start as Hk
  iunfold keeperMap at Hk
  icases Hk with ⟨%km, %tm, %ttl, #Hkm, Htm, #Httl⟩
  (try wp_auto)
  wp_apply (wp_map_lookup2 go.string time.Time.ty km tm token) $$ [$Htm] as Htm
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    wp_apply time.wp_Now as %now -
    wp_apply time.Time.wp_Add as %t' -
    (try wp_auto)
    wp_apply (wp_mapInsert go.string km tm token t') $$ [$Htm] as Htm
    (try wp_auto)
    iapply HΦ
    iunfold keeperMap; iexists km, _, ttl; iframe #; iexact Htm
  (try wp_auto)
  iapply HΦ
  iunfold keeperMap; iexists km, tm, ttl; iframe #; iexact Htm

theorem IntArgValue_uniq_uint64 [go.IntoValInj w64] (n : w64) :
    ∀ z', fmt.IntArgValue (interface.mk go.uint64 #n) z' → z' = uint.Z n := by
  intro z' h
  obtain ⟨n', hv, rfl⟩ := fmt.IntArgValue.of_uint64 h
  rw [go.intoVal_inj hv]

/-- `Sprintf("%s.%d", pre, idx)` for a string and a `uint64` is the simple provider's token. -/
theorem sprintfOut_simpleTok [go.IntoValInj GoString] [go.IntoValInj w64]
    (x : GoString) (n : w64) (out : GoString)
    (h : fmt.SprintfOut go!"%s.%d" [interface.mkOk go.string #x, interface.mkOk go.uint64 #n] out) :
    out = simpleTok x n := by
  have hfmt : go!"%s.%d" = W8 37 :: W8 115 :: W8 46 :: W8 37 :: [W8 100] := rfl
  rw [hfmt] at h
  obtain ⟨o1, rfl, h1⟩ := fmt.SprintfOut.str_inv h
  obtain ⟨o2, rfl, h2⟩ := fmt.SprintfOut.byte_inv (by decide) h1
  obtain ⟨o3, rfl, h3⟩ := fmt.SprintfOut.int_inv (w := 0) (rest := []) (by decide)
    (fmt.IntArgValue.uint64 n) (IntArgValue_uniq_uint64 n) h2
  rw [fmt.SprintfOut.done_inv h3, fmt.decimalPad_zero]
  simp [simpleTok]

/-- `tm.addSimpleToken(token)`: the keeper's map, kept. -/
theorem keeper_add (k : Loc) (token : GoString) :
    {{ keeperMap (GF := GF) k }}
      (App (Val #(methods (go.GoType.PointerType simpleTokenTTLKeeper.ty) go!"addSimpleToken" #k))
        (Val #token))
    {{ RET #(); keeperMap k }} := by
  wp_start as Hk
  iunfold keeperMap at Hk
  icases Hk with ⟨%km, %tm, %ttl, #Hkm, Htm, #Httl⟩
  (try wp_auto)
  wp_apply time.wp_Now as %now -
  wp_apply time.Time.wp_Add as %t' -
  (try wp_auto)
  wp_apply (wp_mapInsert go.string km tm token t') $$ [$Htm] as Htm
  (try wp_auto)
  iapply HΦ
  iunfold keeperMap; iexists km, _, ttl; iframe #; iexact Htm

/-- **A channel a receive may complete on with any outcome** (the index waiter's: etcd's
`wait.WaitTime`'s, closed once the index is applied): a receive's atomic update for any
postcondition that holds of every outcome. -/
def anyRecv (ch : Loc) : IProp GF :=
  iprop(∃ γ : ChanNames, isChan ch γ Unit ∗
    □ (∀ Φ : Unit → Bool → IProp GF, (∀ v ok, Φ v ok) -∗ recvAu γ Unit Φ))

instance anyRecv_persistent (ch : Loc) : Persistent (anyRecv (GF := GF) ch) := by
  unfold anyRecv; infer_instance

/-- **The provider's index waiter** (`indexWaiter`, a `func(uint64) <-chan struct{}` set by
`newTokenProviderSimple`): read-only, and for every index it returns a channel `anyRecv`. -/
def simpleWaitOk (p : Loc) : IProp GF :=
  iprop(∃ iw : GoFunc, tsF go!"indexWaiter" p ↦□ iw ∗
    □ (∀ idx : w64, {{ True }} (App (Val #iw) (Val #idx)) {{ (ch : Loc), RET #ch; anyRecv ch }}))

instance simpleWaitOk_persistent (p : Loc) : Persistent (simpleWaitOk (GF := GF) p) := by
  unfold simpleWaitOk; infer_instance

/-- **The hypothesis on `isValidSimpleToken`** (see the file header): it returns. -/
def ValidSpec : Prop :=
  ∀ (p : Loc) (γt γf : GName) (ctx : GoInterface) (token : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleOk p γt γf }}
      (App (App (Val (p @!! go.GoType.PointerType tokenSimple.ty @!! go!"isValidSimpleToken"))
        (Val #ctx)) (Val #token))
    {{ (b : Bool), RET #b; True }}

/-- **`info`**: a token the map holds was issued to the user it maps to. -/
theorem tokenSimple_info_of (P : IProp GF) [Persistent P] (p : Loc) (γt γf : GName)
    (γa : AuthNames) (hγt : γa.tok = γt) (ctx : GoInterface) (token : GoString) (rev : w64)
    (hValid : {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ P }}
      (App (App (Val (p @!! go.GoType.PointerType tokenSimple.ty @!! go!"isValidSimpleToken"))
        (Val #ctx)) (Val #token))
      {{ (b : Bool), RET #b; True }})
    (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleOk p γt γf ∗ P ∗
      (∀ (a : Loc) (ok : Bool), authInfoRO a ∗
        (if ok then infoBound (.on γa) token a else iprop(True)) -∗ Φ (PairV #a #ok)) ⊢
      WP (App (App (App (Val #(methods (go.GoType.PointerType tokenSimple.ty) go!"info" #p))
        (Val #ctx)) (Val #token)) (Val #rev)) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hok, #HP, HΦ⟩
  wp_method_call; wp_call
  (try wp_auto)
  wp_apply hValid $$ [] as %b -
  · iframe #
  (try wp_auto)
  cases b
  · (try wp_auto)
    iapply HΦ
    isplitr
    · iunfold authInfoRO; ileft; ipureintro; rfl
    simp only [Bool.false_eq_true, ite_false]
    itrivial
  (try wp_auto)
  iunfold simpleOk at Hok
  icases Hok with ⟨%lg, #Hlg, %Hlgnn, #Hmu⟩
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HI⟩
  iunfold simpleLk at HI
  icases HI with ⟨%mp, %m, %k, %ks, %ttl, %S, Hmp, Hm, Hbig, Hauth, Hk, %Hkks, Hks, Httl, %Httlpos⟩
  (try wp_auto)
  wp_apply (wp_map_lookup2 go.string go.string mp m token) $$ [$Hm] as Hm
  (try wp_auto)
  -- the keeper's reset, when the token is in the map and the keeper is set
  wp_join iprop(t_ptr ↦ p ∗ token_ptr ↦ token ∗ tsF go!"simpleTokenKeeper" p ↦ k ∗
      ([∗list] k' ∈ ks, keeperMap k'))
    with [t token Hk Hks] as ⟨t, token, Hk, Hks⟩
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto); iframe t token Hk Hks
    (try wp_auto)
    rcases Hkks with Hkn | Hkm
    · exact absurd Hkn Hif
    icases keepers_acc ks k Hkm $$ Hks with ⟨Hkp, Hback⟩
    wp_apply (keeper_reset k token) $$ [Hkp] as Hkp
    · iframe Hkp
    (try wp_auto)
    ihave Hks := Hback $$ Hkp
    iframe t token Hk Hks
    ipureintro; rfl
  icases big_issued γt γf m token $$ Hbig with ⟨Hbig, #Hiss⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hmp Hm Hbig Hauth Hk Hks Httl]
  · iunfold simpleLk
    iexists mp, m, k, ks, ttl, S
    iframe Hmp Hm Hbig Hauth Hk Hks Httl
    ipureintro; exact ⟨Hkks, Httlpos⟩
  (try wp_auto)
  wp_alloc a as Ha
  ihave %Hann := typedPointsto_not_null _ _ _ $$ Ha
  ihave Haf := typedPointsto_split _ _ _ $$ Ha
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Haf
  ipersist Username
  ipersist Revision
  (try wp_auto)
  iapply HΦ
  isplitr
  · iunfold authInfoRO; iright
    iexists _, rev; isplitr
    · ipureintro; exact Hann
    iframe Username Revision
  cases hlk : m !! token with
  | none => simp only [Option.isSome_none, Bool.false_eq_true, decide_false, ite_false]; itrivial
  | some u =>
    simp only [Option.isSome_some, decide_true, ite_true]
    iunfold infoBound; isplitr
    · ipureintro; exact Hann
    iexists u; simp only [hlk, Option.getD_some]
    iframe Username
    unfold tokOk tokIssued
    simp only [hγt]
    iapply Hiss $$ %u
    ipureintro; rfl

/-- **`info`**: a token the map holds was issued to the user it maps to (over `ValidSpec`). -/
theorem tokenSimple_info (hValid : ValidSpec (GF := GF) (hG := hG)) (p : Loc) (γt γf : GName)
    (γa : AuthNames) (hγt : γa.tok = γt) (ctx : GoInterface) (token : GoString) (rev : w64)
    (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleOk p γt γf ∗
      (∀ (a : Loc) (ok : Bool), authInfoRO a ∗
        (if ok then infoBound (.on γa) token a else iprop(True)) -∗ Φ (PairV #a #ok)) ⊢
      WP (App (App (App (Val #(methods (go.GoType.PointerType tokenSimple.ty) go!"info" #p))
        (Val #ctx)) (Val #token)) (Val #rev)) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hok, HΦ⟩
  iapply tokenSimple_info_of (simpleOk p γt γf) p γt γf γa hγt ctx token rev
  · iintro %Ψ ⟨#Hpkg', #Hok'⟩ HΨ
    iapply (hValid p γt γf ctx token) $$ [] HΨ
    iframe #
  iframe #; iexact HΦ

/-- **`assignSimpleTokenToUser`**, with the right to issue `tok`: `tok` issued to `user`. -/
theorem tokenSimple_assignToUser (p : Loc) (γt γf : GName) (γa : AuthNames) (hγt : γa.tok = γt)
    (hγf : γa.fresh = γf) (user tok : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleOk p γt γf ∗
        tokFresh γa tok }}
      (App (App (Val #(methods (go.GoType.PointerType tokenSimple.ty) go!"assignSimpleTokenToUser" #p))
        (Val #user)) (Val #tok))
    {{ RET #(); tokIssued γa tok user }} := by
  wp_start as ⟨#Hok, Hfr⟩
  iunfold simpleOk at Hok
  icases Hok with ⟨%lg, #Hlg, %Hlgnn, #Hmu⟩
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HI⟩
  iunfold simpleLk at HI
  icases HI with ⟨%mp, %m, %k, %ks, %ttl, %S, Hmp, Hm, Hbig, Hauth, Hk, %Hkks, Hks, Httl, %Httlpos⟩
  -- issue the token (whichever branch is taken)
  iunfold tokFresh at Hfr
  rw [hγf]
  imod tokIssue ⟨γt, γt, γt, γt⟩ S tok user $$ Hauth with ⟨%S', Hauth, #Hiss⟩
  (try wp_auto)
  wp_if_destruct
  · -- no keeper (auth disabled): the token is not stored
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hmp Hm Hbig Hauth Hk Hks Httl]
    · iunfold simpleLk
      iexists mp, m, null, ks, ttl, S'
      iframe Hmp Hm Hbig Hauth Hk Hks Httl
      ipureintro; exact ⟨Or.inl rfl, Httlpos⟩
    (try wp_auto)
    iapply HΦ
    unfold tokIssued; rw [hγt]; iexact Hiss
  (try wp_auto)
  wp_apply (wp_map_lookup2 go.string go.string mp m tok) $$ [$Hm] as Hm
  (try wp_auto)
  cases hlk : m !! tok with
  | some u =>
    icases (BigSepM.bigSepM_lookup_acc hlk).1 $$ Hbig with ⟨⟨-, Hf2⟩, -⟩
    ihave %Hne := ghostMapElem_ne γf tok tok (DFrac.own 1) () () $$ Hfr Hf2
    exact absurd rfl Hne
  | none =>
  (try wp_auto)
  wp_apply (wp_mapInsert go.string mp m tok user) $$ [$Hm] as Hm
  (try wp_auto)
  rcases Hkks with Hkn | Hkm
  · exact absurd Hkn Hif
  icases keepers_acc ks k Hkm $$ Hks with ⟨Hkp, Hback⟩
  wp_apply (keeper_add k tok) $$ [$Hkp] as Hkp
  ihave Hks := Hback $$ Hkp
  (try wp_auto)
  ihave Hbig : [∗map] t ↦ u ∈ (<[tok := user]> m),
      iprop(ghostMapElem (GF := GF) γt (t, u) DFrac.discard () ∗ ghostMapElem γf t (DFrac.own 1) ()) $$
      [Hbig Hfr]
  · iapply (BigSepM.bigSepM_insert hlk).2
    iframe Hbig Hfr
    iunfold tokIssued at Hiss; iexact Hiss
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hmp Hm Hbig Hauth Hk Hks Httl]
  · iunfold simpleLk
    iexists mp, _, k, ks, ttl, S'
    iframe Hmp Hm Hbig Hauth Hk Hks Httl
    ipureintro; exact ⟨Or.inr Hkm, Httlpos⟩
  (try wp_auto)
  iapply HΦ
  unfold tokIssued; rw [hγt]; iexact Hiss

/-- **`assign`**, on an `Authenticate` context: a token issued to the user, or an error. -/
theorem tokenSimple_assign (p : Loc) (γt γf : GName) (γa : AuthNames) (hγt : γa.tok = γt)
    (hγf : γa.fresh = γf) (ctx : GoInterface) (user : GoString) (rev : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleOk p γt γf ∗
        authnCtx (.on γa) ctx }}
      (App (App (App (Val #(methods (go.GoType.PointerType tokenSimple.ty) go!"assign" #p))
        (Val #ctx)) (Val #user)) (Val #rev))
    {{ (t : GoString) (err : GoInterface), RET (PairV #t #err);
        ⌜err ≠ GoInterface.nil⌝ ∨ tokOk (.on γa) t user }} := by
  wp_start as ⟨#Hok, Hctx⟩
  iunfold authnCtx at Hctx
  icases Hctx with ⟨%ci, %idx, %pre, %Hci, #HV, Hfr⟩
  subst Hci
  (try wp_auto)
  wp_apply HV as %v1 %Hv1
  obtain rfl := Hv1.1 _ rfl
  (try wp_auto)
  wp_apply HV as %v2 %Hv2
  obtain rfl := Hv2.2 _ rfl
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  (try wp_auto)
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  have hl : [interface.mkOk go.string #pre, GoInterface.nil].set (sint.nat (W64 (0 + 1)))
      (interface.mkOk go.uint64 #idx) = [interface.mkOk go.string #pre, interface.mkOk go.uint64 #idx] := by
    rfl
  rw [hl]
  wp_apply (fmt.wp_Sprintf go!"%s.%d" _ _ _
      (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_int (interface.mk go.uint64 #idx) _ _
        (fmt.IntArgValue.uint64 idx) fmt.ArgsWf.nil))) $$ [$Hasl] as %tok ⟨-, %Htok⟩
  have htok := sprintfOut_simpleTok pre idx tok Htok
  subst htok
  (try wp_auto)
  wp_apply (tokenSimple_assignToUser p γt γf γa hγt hγf user (simpleTok pre idx)) $$ [Hfr] as #Hiss
  · iframe #; iunfold freshOk at Hfr; iexact Hfr
  (try wp_auto)
  iapply HΦ
  iright
  iunfold tokOk; iexact Hiss

end proof

section proof_lc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`isValidSimpleToken`** (the auth plan's S5c, 2026-10-25), on a context (Perennial's
`context.isContext`) and with the provider's index waiter: it returns (`strings.Split`,
`strconv.ParseUint`, then a `select` on the waiter's channel and the context's `Done`). -/
theorem tokenSimple_isValid (p : Loc) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (token : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleWaitOk p ∗
        context.isContext ci cd }}
      (App (App (Val (p @!! go.GoType.PointerType tokenSimple.ty @!! go!"isValidSimpleToken"))
        (Val #(GoInterface.ok ci))) (Val #token))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as ⟨#Hw, #Hctx⟩
  (try wp_auto)
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_apply strings.wp_Split token go!"." (by decide) $$ [$Hstr] as %sl ⟨Hsl, -⟩
  ihave %Hslen := ownSlice_len $$ Hsl
  (try wp_auto)
  ihave #Hctx2 : iprop(context.isContextDef ci cd) $$ [Hctx]
  · iexact Hctx
  iunfold context.isContextDef at Hctx2
  icases Hctx2 with ⟨-, #HDoneC, -⟩
  iunfold simpleWaitOk at Hw
  icases Hw with ⟨%iw, #Hiw, #Hiws⟩
  wp_if_destruct
  · -- two fields: the second parsed as the index
    have hb : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z sl.len := by
      rw [Hif]; constructor <;> decide
    obtain ⟨s0, s1, hsp⟩ : ∃ s0 s1, strings.split token [46#8] = [s0, s1] := by
      have h2 : (strings.split token [46#8]).length = 2 := by rw [Hslen.1, Hif]; rfl
      match hx : strings.split token [46#8], h2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    rw [ite_eq_left hb]
    wp_apply wp_load_slice_index sl (sint.Z (W64 1)) _ _ s1 hb.1 $$ [$Hsl] as Hsl
    · ipureintro; rw [hsp]; rfl
    (try wp_auto)
    ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
    · iPkgInit
    wp_apply (_root_.Perennial.strconv.wp_ParseUint s1 (W64 10) (W64 0) (by decide) (by decide) (by decide)
      (by decide)) $$ [$Hsc] as %x %err Hres
    cases hp : internal.strconv.parseUint s1 10 0 <;>
      simp only [hp]
    · icases Hres with %Hok
      obtain ⟨rfl, rfl⟩ := Hok
      (try wp_auto)
      wp_apply Hiws as %ch0 #Hch0
      (try wp_auto)
      wp_apply +noauto HDoneC as %ch1 %γ1 #Hdone1
      (try wp_auto)
      iunfold anyRecv at Hch0
      icases Hch0 with ⟨%γ0, #Hic0, #Hau0⟩
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch0, γ0
        isplit
        · ipureintro; rfl
        isplit
        · iexact Hic0
        iapply Hau0
        iintro %v %ok
        (try wp_auto)
        iapply HΦ; itrivial
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
        isplit
        · ipureintro; rfl
        isplit
        · iapply context.isContextDone_is_chan $$ Hdone1
        iapply context.isContextDone_receive _ _ _ _ $$ Hdone1
        iintro -
        (try wp_auto)
        iapply HΦ; itrivial
      iapply BigAndL.bigAndL_nil.2
      itrivial
    all_goals
      iunfold strconv.numErrorOf at Hres
      icases Hres with ⟨-, %l, %e, %Herr, -⟩
      subst Herr
      (try wp_auto)
      iapply HΦ; itrivial
  · (try wp_auto); iapply HΦ; itrivial

/-- **`info` on a context** (the auth plan's S5c): a token the map holds was issued to the user it
maps to, with no hypothesis on `isValidSimpleToken` (`tokenSimple_isValid`). -/
theorem tokenSimple_info_ctx (p : Loc) (γt γf : GName) (γa : AuthNames) (hγt : γa.tok = γt)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (token : GoString) (rev : w64)
    (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleOk p γt γf ∗
      simpleWaitOk p ∗ context.isContext ci cd ∗
      (∀ (a : Loc) (ok : Bool), authInfoRO a ∗
        (if ok then infoBound (.on γa) token a else iprop(True)) -∗ Φ (PairV #a #ok)) ⊢
      WP (App (App (App (Val #(methods (go.GoType.PointerType tokenSimple.ty) go!"info" #p))
        (Val #(GoInterface.ok ci))) (Val #token)) (Val #rev)) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hok, #Hw, #Hctx, HΦ⟩
  iapply tokenSimple_info_of iprop(simpleWaitOk p ∗ context.isContext ci cd) p γt γf γa hγt
    (GoInterface.ok ci) token rev
  · iintro %Ψ ⟨#Hpkg', #Hw', #Hctx'⟩ HΨ
    iapply (tokenSimple_isValid p ci cd token) $$ [] HΨ
    iframe #
  iframe #; iexact HΦ

end proof_lc

end auth

end EtcdGrove
end Perennial
