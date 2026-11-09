/-
Lean-first (no Rocq counterpart).

The proof of `(*store).GuaranteedUpdate`: the prepared key, tracing (no-ops), the destination's
`reflect.Value`, then (as `conditionalDelete`'s, D30n) the first read's names, its invariant with
the caller's token `W` made only when a read is made: at once without a cached object, or later
on the cached state (`refreshOnError`'s re-read after a failed check, or the no-op path's re-read,
`store.go:556`). The loop's invariant: the state `s` (`stFrom`; `szOk`, what the size premises give
for it), and either the cached state with `W`, the names' ghost state and D1's facts, or a read of
`s` at `σ` (`rdOf`: the key's key-value, or the zero state with `ignoreNotFound`) with the
caller's result if `σ` hands, else `W`. A failed precondition or `tryUpdate`'s error is the model's
answer (`update_cur_pre`, `update_cur_err`) at the read's state where the key is the state's
(`rd_current`; on a cached state the re-read's, when the key did not move: `stFrom_rd_item`); an
unchanged encoding is the model's no-op at the read's state (`rd_noop`), and on a cached state at
the re-read's, whose data is then the cached object's encoding, so its object (`rd_data`), on which
D1 makes the preconditions and `tryUpdate` answer as on the cached one; otherwise `updateOnce`
either answers (an error, or the write) or, on a conflict, gives the next iteration's reading.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__GuaranteedUpdate
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__prepareKey
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getCurrentState
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getStateFromObject
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__updateState
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__updateOnce
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.refreshOnError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.getTypeName
public import Spec.k8s_io.apiserver.pkg.storage.Preconditions__Check
public import Spec.k8s_io.apimachinery.pkg.conversion.EnforcePtr
public import Spec.k8s_io.component_base.tracing.Start
public import Spec.k8s_io.component_base.tracing.Span__AddEvent
public import Spec.k8s_io.component_base.tracing.Span__End
public import Spec.go_opentelemetry_io.otel.attribute.String
public import Spec.go_opentelemetry_io.otel.attribute.Int
public import Spec.k8s_io.apiserver.pkg.audit.GetAuditIDTruncated
public import Perennial.Proof.bytes.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

section helpers
variable [go_etcd_io.etcd.client.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- What `updateOnce` needs of the result's size, for the state `s` (from the size premises). -/
private def szOk {E : Type} {Obj : Type} [DecidableEq Obj] (c : StoreCfg GF Obj)
    (f : Obj → Nat → Except E Obj) (s : OState Obj) : Prop :=
  ∀ o', f s.o (uint.nat s.rev) = .ok o' → (!s.stale && decide (c.S.encode o' = s.data)) = false →
    c.S.storedSizeOk o'

private theorem rd_szOk {E : Type} {Obj : Type} [DecidableEq Obj] (c : StoreCfg GF Obj) (key : GoString)
    (ign : Bool) (f : Obj → Nat → Except E Obj) (σ : KVState) (s : OState Obj)
    (hfsz : ∀ (v d : GoString) (stl : Bool) (o : Obj) (n : Nat) (o' : Obj), v.length ≤ etcdKeyMax →
      c.S.fromS v = some (d, stl) → c.S.decode d = some o → f o n = .ok o' →
      (stl = true ∨ c.S.encode o' ≠ d) → c.S.storedSizeOk o')
    (hzsz : ign = true → ∀ o', f c.S.zero 0 = .ok o' → c.S.storedSizeOk o')
    (hrd : rdOf c key ign σ s) (hv : ∀ v ∈ σ.kvs, v.value.length ≤ 2 ^ 27) : szOk c f s := by
  rcases hrd with ⟨kv, hf, hs⟩ | ⟨hf, hi, rfl⟩
  · intro o' hok hw
    refine hfsz kv.value s.data s.stale s.o _ o' (hv kv (mvcc.findKey_mem hf)) hs.2.1 hs.2.2.1 hok ?_
    cases h : s.stale
    · rw [h] at hw; right; simpa using hw
    · left; rfl
  · intro o' hok _
    exact hzsz hi o' (by simpa [zeroSt] using hok)

private theorem rdOf_current {Obj : Type} [DecidableEq Obj] (c : StoreCfg GF Obj) (key : GoString)
    (ign : Bool) (σ : KVState) (s : OState Obj) (hrd : rdOf c key ign σ s) : s.current = true := by
  rcases hrd with ⟨kv, -, hs⟩ | ⟨-, -, rfl⟩
  · exact hs.2.2.2
  · rfl

/-- A read whose data is an object's encoding read that object. -/
private theorem rd_data {Obj : Type} [DecidableEq Obj] (c : StoreCfg GF Obj) (key : GoString)
    (ign : Bool) (σ : KVState) (s : OState Obj) (hrd : rdOf c key ign σ s) (o : Obj)
    (h : s.data = c.S.encode o) : s.o = o := by
  rcases hrd with ⟨kv, -, hs⟩ | ⟨-, -, rfl⟩
  · have := hs.2.2.1
    rw [h, c.S.decode_encode] at this
    exact (Option.some.inj this).symm
  · exact absurd h.symm (c.S.encode_ne_nil o)

/-- The model's no-op at a read's state. -/
private theorem rd_noop {E : Type} {Obj : Type} [DecidableEq Obj] (c : StoreCfg GF Obj) (key : GoString)
    (hpk : c.pfx <+: key) (ign : Bool) (σ : KVState) (s : OState Obj) (hrd : rdOf c key ign σ s)
    (pre : Obj → Nat → Bool) (f : Obj → Nat → Except E Obj) (o' : Obj)
    (hpre : pre s.o (uint.nat s.rev) = true) (hok : f s.o (uint.nat s.rev) = .ok o')
    (hn : (!s.stale && decide (c.S.encode o' = s.data)) = true) :
    (c.abs σ).update key ign c.S.zero pre f = (c.abs σ, .obj s.o (uint.nat s.rev)) := by
  rcases hrd with ⟨kv, hf, hs⟩ | ⟨-, -, rfl⟩
  · exact update_skip c σ key hpk kv hf s hs ign c.S.zero pre hpre f o' hok hn
  · exfalso
    simp only [zeroSt, Bool.not_false, Bool.true_and] at hn
    exact c.S.encode_ne_nil o' (of_decide_eq_true hn)

/-- `stAt`'s two shapes: "not found" (without `ignoreNotFound`), or a read's state. -/
private theorem stAt_cases {Obj : Type} [DecidableEq Obj] (c : StoreCfg GF Obj) (key : GoString)
    (ign : Bool) (σ : KVState) (st : Loc) (e : GoInterface) :
    stAt c key ign σ st e ⊢ (⌜mvcc.findKey key σ.kvs = none ∧ ign = false ∧ st = null⌝ ∗
        storageErrIs e (W64 1) key (W64 (σ.rev : Int))) ∨
      (⌜e = GoInterface.nil⌝ ∗ ∃ s, ownState c st s ∗ ⌜rdOf c key ign σ s⌝) := by
  unfold stAt
  rcases hf : mvcc.findKey key σ.kvs with _ | kv
  · cases ign
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iintro ⟨%h, H⟩
      ileft
      iframe H
      ipureintro; simp [h]
    · simp only [↓reduceIte]
      iintro ⟨%h, H⟩
      iright
      isplitr
      · ipureintro; exact h
      iexists zeroSt c
      iframe H
      ipureintro; exact .inr ⟨hf, rfl, rfl⟩
  · iintro ⟨%h, %s, H, %hs⟩
    iright
    isplitr
    · ipureintro; exact h
    iexists s
    iframe H
    ipureintro; exact .inl ⟨kv, hf, hs⟩

/-- `updateOnce`'s conflict's token, in the first read's form. -/
private theorem ht_conv {Obj : Type} [DecidableEq Obj] (c : StoreCfg GF Obj) (key : GoString)
    (hand : KVState → Bool) (W : IProp GF) (Φ : KVState → IProp GF) (σ : KVState) :
    (if hand σ then Φ σ else W) ⊢ (if hand σ then iprop(∃ σ1, Φ σ1 ∗
      ⌜(c.abs σ1).items key = (c.abs σ).items key ∧ σ1.rev = σ.rev⌝) else W) := by
  cases hand σ
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro H
    iexact H
  · simp only [↓reduceIte]
    iintro H
    iexists σ
    iframe H
    ipureintro; exact ⟨rfl, rfl⟩

/-- **The answer at a state where the model's step is the identity** (the token handed there). -/
private theorem gu_answer {E : Type} [KUserErr E] {Obj : Type} [DecidableEq Obj] (c : StoreCfg GF Obj)
    (key : GoString) (ign : Bool) (pre : Obj → Nat → Bool) (f : Obj → Nat → Except E Obj)
    (W : IProp GF) (Φ : KVState → IProp GF) (σ : KVState) (resp : KResp Obj E) (err dest : GoInterface)
    (h : (c.abs σ).update key ign c.S.zero pre f = (c.abs σ, resp)) :
    (if stepHand c (updStep key ign c.S.zero pre f) σ then iprop(∃ σ1, Φ σ1 ∗
        ⌜(c.abs σ1).items key = (c.abs σ).items key ∧ σ1.rev = σ.rev⌝) else W) ∗
      respIs c resp err dest ⊢ updOut c key ign c.S.zero pre f Φ err dest := by
  have hh := hand_true c (updStep key ign c.S.zero pre f) σ (by simp [updStep, h])
  rw [hh]
  simp only [↓reduceIte]
  iintro ⟨⟨%σ1, HΦ1, %Hsame⟩, Hr⟩
  iunfold updOut
  iright
  iexists σ1
  iframe HΦ1
  rw [update_local key ign c.S.zero pre f (c.abs σ1) (c.abs σ) Hsame.1
    (by rw [abs_rv, abs_rv, Hsame.2]), h]
  iexact Hr

end helpers

set_option hygiene false in
/-- The model's step of the update. -/
local notation "STEP" => updStep pk ign c.S.zero (c.S.preOk pr) f

set_option hygiene false in
/-- A return: the deferred `span.End`, then the caller's postcondition. -/
local macro "gu_ret" : tactic => `(tactic| (
  (try wp_auto)
  (try wp_for_post)
  wp_apply wp_End spn _ $$ []
  · iframe #
    ipureintro; exact Hspn
  (try wp_auto)
  iapply HΦ))

set_option hygiene false in
/-- After `updateOnce` (`Hd`): an error, the write, or a conflict's next reading. -/
local macro "gu_once" : tactic => `(tactic| (
  icases Hd with (⟨#Hde, Hout⟩ | ⟨%Hok, %σ', HΦu, Hresp⟩ | ⟨%Hok, Hout, %σ', #Hfs', %Hvals', Hat, HT'⟩)
  · -- an error
    ihave %Hne := unkErr_ne c uerr $$ Hde
    rcases uerr with ei | _
    rotate_left
    · exact absurd rfl Hne
    gu_ret
    iunfold updOut
    ileft
    iframe Hout
    iexact Hde
  · -- written
    obtain ⟨rfl, rfl⟩ := Hok
    gu_ret
    iunfold updOut
    iright
    iexists σ'
    iframe HΦu Hresp
  · -- a conflict
    subst Hok
    ihave HT' := ht_conv c pk (stepHand c STEP) W Φu σ' $$ HT'
    ihave Hat := stAt_cases c pk ign σ' st' uerr $$ Hat
    icases Hat with (⟨%Hn, Herr⟩ | ⟨%He, %s', Hos', %Hrd'⟩)
    · obtain ⟨hf', rfl, rfl⟩ := Hn
      iunfold storageErrIs at Herr
      icases Herr with ⟨%ep, %Hep, #Hep⟩
      subst Hep
      gu_ret
      iapply (gu_answer c pk false (c.S.preOk pr) f W Φu σ' _ _ _
        (update_none c σ' pk hf' c.S.zero (c.S.preOk pr) f))
      iframe HT'
      simp only [respIs, storageErrIs]
      isplitl []
      · iexists ep
        iframe Hep
        ipureintro; rfl
      iexists o0, rv0
      iexact Hout
    · subst He
      ihave Hfr := stFrom_rdOf c pk ign σ' s' Hrd' $$ Hfs'
      icases Hfr with ⟨#Hfrom', %Hsr'⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists st', s'
      iframe origState Hos' Hout Hfrom'
      isplitr
      · ipureintro; exact ⟨Hsr'.1, rd_szOk c pk ign f σ' s' hfsz hzsz Hrd' Hvals'⟩
      iright
      iexists σ'
      iframe Hfs' HT'
      ipureintro; exact Hrd'))

set_option hygiene false in
/-- `GuaranteedUpdate`'s loop after a failed check (`Preconditions.Check`'s or `tryUpdate`'s error
`ok ei`, the state's object given away, `Hx`; `hmod`, the model's answer on the state's current
object, `Hε` its shape): `refreshOnError`, then on a cached state its re-read through the first
read's invariant. -/
local macro "gu_refresh" : tactic => `(tactic| (
  icases Hph with (⟨%HD1, HW, Hlc, Hc, Htok, Hp⟩ | ⟨%σ, #Hfs, %Hrd, HT⟩)
  · -- the cached state: the re-read is the first read
    have Hcur : s.current = false := HD1.1
    ihave %Hcd := stFrom_cached c pk s $$ Hfrom
    imod (rwInv_alloc_at γc γt γp c pk (stepHand c STEP) W Φu ⊤) $$ [HW Hc] with #Hrw
    · iframe HW Hc
    ihave Hmk := (rwInv_maker γc γt γp c pk STEP (stepHand c STEP)
      (handOk_upd c pk ign c.S.zero (c.S.preOk pr) f) W Φu) $$ [Hp]
    · iframe Hrw Hp Hau
    wp_apply (wp_refresh Obj c st s _ gf x' pk ign (rdQ γc γp c pk (stepHand c STEP))) $$ [Hx Hmk]
      as %st' %err' Hr
    · isimp only [Hcur, Bool.false_eq_true, ↓reduceIte]
      iframe Hx Hgf Hmk
    isimp only [Hcur, Bool.false_eq_true, ↓reduceIte] at Hr
    icases Hr with (#Hu | ⟨%σ, %e0, #Hrq, %Hvals, Hat, %He'⟩)
    · ihave %Hne := unkErr_ne c err' $$ Hu
      rcases err' with ei' | _
      rotate_left
      · exact absurd rfl Hne
      gu_ret
      iunfold updOut
      ileft
      isplitr
      · iexact Hu
      iexists o0, rv0
      iexact Hout
    ihave #Hrq' := Hrq
    iunfold rdQ at Hrq'
    icases Hrq' with ⟨#Hfs, -, -⟩
    imod (rwInv_after γc γt γp c pk STEP (stepHand c STEP)
      (handOk_upd c pk ign c.S.zero (c.S.preOk pr) f) W Φu σ) $$ [Htok Hrq Hlc] with HT
    · iframe Hrw Htok Hrq Hlc
    ihave Hat := stAt_cases c pk ign σ st' e0 $$ Hat
    icases Hat with (⟨%Hn, Herr⟩ | ⟨%He, %s0, Hos', %Hrd⟩)
    · obtain ⟨hf, rfl, rfl⟩ := Hn
      iunfold storageErrIs at Herr
      icases Herr with ⟨%ep, %Hep, #Hep⟩
      subst Hep
      rw [if_neg (fun h => by cases h.1)] at He'
      subst He'
      gu_ret
      iapply (gu_answer c pk false (c.S.preOk pr) f W Φu σ _ _ _
        (update_none c σ pk hf c.S.zero (c.S.preOk pr) f))
      iframe HT
      simp only [respIs, storageErrIs]
      isplitl []
      · iexists ep
        iframe Hep
        ipureintro; rfl
      iexists o0, rv0
      iexact Hout
    subst He
    by_cases hm : kubernetes.modAt pk σ = s.rev
    · -- the key did not move: the check's error, the model's answer at the read's state
      rw [if_pos ⟨rfl, hm⟩] at He'
      subst He'
      ihave %Hit := (stFrom_rd_item c pk hpfx s (Hcd Hcur).2.2 σ hm) $$ [Hfrom Hfs]
      · iframe Hfrom Hfs
      obtain ⟨b, hb⟩ := Hit
      have hid := hmod (c.abs σ) (current_of_item _ pk ign c.S.zero _ _ b hb)
      gu_ret
      iapply (gu_answer c pk ign (c.S.preOk pr) f W Φu σ _ _ _ hid)
      iframe HT
      iapply Hε
      iexact Hout
    · -- the key moved: the next iteration from the read
      rw [if_neg (fun h => hm h.2)] at He'
      subst He'
      ihave Hfr := stFrom_rdOf c pk ign σ s0 Hrd $$ Hfs
      icases Hfr with ⟨#Hfrom', %Hsr'⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists st', s0
      iframe origState Hos' Hout Hfrom'
      isplitr
      · ipureintro; exact ⟨Hsr'.1, rd_szOk c pk ign f σ s0 hfsz hzsz Hrd Hvals⟩
      iright
      iexists σ
      iframe Hfs HT
      ipureintro; exact Hrd
  · -- a read's state: current, the check's error back
    have Hcur : s.current = true := rdOf_current c pk ign σ s Hrd
    wp_apply (wp_refresh Obj c st s _ gf x' pk ign (rdQ γc γp c pk (stepHand c STEP))) $$ [Hx]
      as %st' %err' Hr
    · isimp only [Hcur, ↓reduceIte]
      iframe Hx
    isimp only [Hcur, ↓reduceIte] at Hr
    icases Hr with ⟨%Heq, -⟩
    obtain ⟨rfl, rfl⟩ := Heq
    have hid := hmod (c.abs σ) (rd_current c pk hpfx ign σ s Hrd)
    gu_ret
    iapply (gu_answer c pk ign (c.S.preOk pr) f W Φu σ _ _ _ hid)
    iframe HT
    iapply Hε
    iexact Hout))

set_option maxHeartbeats 1600000 in
theorem store.GuaranteedUpdate.wp_proof
    (wp_prepareKey : store.prepareKey.spec (GF := GF) (hG := hG))
    (wp_getTypeName : getTypeName.spec (GF := GF) (hG := hG))
    (wp_EnforcePtr : conversion.EnforcePtr.spec (GF := GF) (hG := hG))
    (wp_getCur : store.getCurrentState.spec (GF := GF) (hG := hG))
    (wp_getStateFromObject : store.getStateFromObject.spec (GF := GF) (hG := hG))
    (wp_Check : storage.Preconditions.Check.spec (GF := GF) (hG := hG))
    (wp_updateState : store.updateState.spec (GF := GF) (hG := hG))
    (wp_updateOnce : store.updateOnce.spec (GF := GF) (hG := hG))
    (wp_refresh : refreshOnError.spec (GF := GF) (hG := hG))
    (wp_Start : tracing.Start.spec (GF := GF) (hG := hG))
    (wp_AddEvent : tracing.Span.AddEvent.spec (GF := GF) (hG := hG))
    (wp_End : tracing.Span.End.spec (GF := GF) (hG := hG))
    (wp_String : «attribute».String.spec (GF := GF) (hG := hG))
    (wp_Int : «attribute».Int.spec (GF := GF) (hG := hG))
    (wp_GetAuditIDTruncated : audit.GetAuditIDTruncated.spec (GF := GF) (hG := hG)) :
    store.GuaranteedUpdate.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ E _ sp c ci cd key dest o0 rv0 ign pp pr cx ca f uf W _ Φu k
  wp_start as ⟨#Hst, %Hpre, #Hctx, #Hce, Hout, #Hpp, Hca, HW, #Hau, #Hup⟩
  obtain ⟨hk, hkl, hfsz, hzsz, hcsz, hD1⟩ := Hpre
  ihave Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt,
    #Hkc, #Hcl, #Hone, #Hregs, #Hcon, -⟩
  iunfold contractOk at Hcon
  icases Hcon with ⟨%Hty, #Henc, #Hver, #Htr, #Hdec, #Hzero, #Hmeta⟩
  ihave #Ptr : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing $$ []
  · iPkgInit
  ihave #Pat : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.«attribute» $$ []
  · iPkgInit
  ihave #Pau : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.audit $$ []
  · iPkgInit
  ihave #Pcv : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.conversion $$ []
  · iPkgInit
  ihave #Psg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  ihave #Pby : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  ihave Fgr' := Fgr
  iStructNamed Fgr'
  -- the first read's names (its invariant, with the caller's token, made at the first read)
  ihave Hnames := rwNames_alloc (GF := GF)
  imod Hnames with ⟨%γc, %γt, %γp, Hc, Htok, Hp⟩
  have hR : ∀ R0 m σ, rdQ (GF := GF) γc γp c (c.pathPrefix ++ k) (stepHand c (updStep (c.pathPrefix ++ k) ign c.S.zero (c.S.preOk pr) f)) R0 m σ ⊢
      ⌜kvWf c σ⌝ := fun R0 m σ => by
    iintro #H
    iunfold rdQ at H
    icases H with ⟨#Hf, -, -⟩
    iunfold rdFacts at Hf
    icases Hf with ⟨%h, -⟩
    ipureintro; exact h.1
  have hpfx : c.pfx <+: c.pathPrefix ++ k := prepareKeyM_prefix _ _ _ _ _ hk
  ihave %Hptr := c.S.objAt_ptr dest o0 rv0 $$ Hout
  obtain ⟨p, hp, rfl⟩ := Hptr
  ihave %Hdn := c.S.objAt_ne_nil _ o0 rv0 $$ Hout
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_prepareKey sp c.resourcePrefix c.pathPrefix key false $$ [] as %pk %perr %Hpk
  · iframe #
  rw [hk] at Hpk
  obtain ⟨rfl, rfl⟩ := Hpk
  (try wp_auto)
  wp_apply wp_GetAuditIDTruncated as %aid -
  wp_apply wp_String as %kv0 -
  wp_apply wp_String as %kv1 -
  (try wp_auto)
  wp_apply wp_getTypeName _ $$ [] as %tn -
  · iframe #
    ipureintro; exact Hdn
  wp_apply wp_String as %kvt -
  (try wp_auto)
  wp_apply wp_String as %kv2 -
  (try wp_auto)
  wp_apply wp_String as %kv3 -
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply wp_Start ci cd _ _ $$ [] as %ci' %spn ⟨%Hspn, #Hctx', #Hce'⟩
  · iframe #
  (try wp_auto)
  wp_apply wp_EnforcePtr c.S.objTy p $$ [] as %v %eerr %Hen'
  · iframe #
    ipureintro; exact hp
  obtain ⟨rfl, Hv⟩ := Hen'
  wp_auto_lc 1
  wp_apply (wp_getCur Obj sp c ci' cd go!"updateGet" (c.pathPrefix ++ k) v p ign
      (rdQ γc γp c (c.pathPrefix ++ k) (stepHand c (updStep (c.pathPrefix ++ k) ign c.S.zero (c.S.preOk pr) f))) hpfx hkl hR (by decide)) $$ [] as %gf #Hgf
  · iframe #
    ipureintro; exact Hv
  (try wp_auto)
  clear hR
  generalize c.pathPrefix ++ k = pk at hpfx hkl ⊢
  rcases ca with _ | ⟨o1, r1⟩
  focus
    -- no cached object: the first read, through the invariant
    iunfold cachedOk at Hca
    icases Hca with %Hcx
    subst Hcx
    (try wp_auto)
    imod (rwInv_alloc_at γc γt γp c pk (stepHand c STEP) W Φu ⊤) $$ [HW Hc] with #Hrw
    · iframe HW Hc
    ihave Hmk := (rwInv_maker γc γt γp c pk STEP (stepHand c STEP)
      (handOk_upd c pk ign c.S.zero (c.S.preOk pr) f) W Φu) $$ [Hp]
    · iframe Hrw Hp Hau
    ihave #Hgf' := Hgf
    iunfold getStateOk at Hgf'
    wp_apply Hgf' $$ [Hmk] as %st %err Hr
    · iexact Hmk
    icases Hr with (#Herr | ⟨%σ, #Hrq, %Hvals, Hat⟩)
    · ihave %Hne := unkErr_ne c err $$ Herr
      rcases err with ei | _
      rotate_left
      · exact absurd rfl Hne
      gu_ret
      iunfold updOut
      ileft
      isplitr
      · iexact Herr
      iexists o0, rv0
      iexact Hout
    ihave #Hrq' := Hrq
    iunfold rdQ at Hrq'
    icases Hrq' with ⟨#Hfs, -, -⟩
    imod (rwInv_after γc γt γp c pk STEP (stepHand c STEP)
      (handOk_upd c pk ign c.S.zero (c.S.preOk pr) f) W Φu σ) $$ [Htok Hrq Hlc1] with HT
    · iframe Hrw Htok Hrq Hlc1
    ihave Hat := stAt_cases c pk ign σ st err $$ Hat
    icases Hat with (⟨%Hn, Herr⟩ | ⟨%He, %s0, Hos, %Hrd⟩)
    · obtain ⟨hf, rfl, rfl⟩ := Hn
      iunfold storageErrIs at Herr
      icases Herr with ⟨%ep, %Hep, #Hep⟩
      subst Hep
      gu_ret
      iapply (gu_answer c pk false (c.S.preOk pr) f W Φu σ _ _ _
        (update_none c σ pk hf c.S.zero (c.S.preOk pr) f))
      iframe HT
      simp only [respIs, storageErrIs]
      isplitl []
      · iexists ep
        iframe Hep
        ipureintro; rfl
      iexists o0, rv0
      iexact Hout
    subst He
    (try wp_auto)
    wp_apply wp_AddEvent spn _ _ $$ []
    · iframe #
      ipureintro; exact Hspn
    (try wp_auto)
    ihave Hfr := stFrom_rdOf c pk ign σ s0 Hrd $$ Hfs
    icases Hfr with ⟨#Hfrom, %Hsr⟩
    ihave HI : (∃ (st : Loc) (s : OState Obj),
        "origState" ∷ origState_ptr ↦ st ∗ "Hos" ∷ ownState c st s ∗
        "Hout" ∷ c.S.objAt (interface.mkOk (go.GoType.PointerType c.S.objTy) #p) o0 rv0 ∗
        "#Hfrom" ∷ stFrom c pk s ∗ "%Hsr" ∷ ⌜(s.rev = W64 0 → ign = true) ∧ szOk c f s⌝ ∗
        "Hph" ∷ ((⌜s.current = false ∧ pr.rv = none ∧ ∀ n, f s.o n = f s.o (uint.nat s.rev)⌝ ∗
              W ∗ £ 1 ∗ dghostVar γc (DFrac.own 1) (none : Option KVState) ∗
              dghostVar γt (DFrac.own 1) () ∗
              dghostVar γp (DFrac.own 1) (none : Option (w64 × w64))) ∨
            (∃ σ : KVState, rdFacts c σ ∗ ⌜rdOf c pk ign σ s⌝ ∗
              (if stepHand c STEP σ then iprop(∃ σ1, Φu σ1 ∗
                ⌜(c.abs σ1).items pk = (c.abs σ).items pk ∧ σ1.rev = σ.rev⌝) else W))) :
        IProp GF) $$ [origState Hos HT Hout]
    · iexists st, s0
      iframe origState Hos Hout Hfrom
      isplitr
      · ipureintro; exact ⟨Hsr.1, rd_szOk c pk ign f σ s0 hfsz hzsz Hrd Hvals⟩
      iright
      iexists σ
      iframe Hfs HT
      ipureintro; exact Hrd
    iclear Hfs Hrq Hfrom Hrw Hgf'
    clear Hrd Hsr Hvals σ s0 st
  rotate_left
  focus
    -- the cached object: its state, the token kept
    iunfold cachedOk at Hca
    icases Hca with ⟨%Hr1, Hcobj, #Hver1⟩
    ihave %Hcn := c.S.objAt_ne_nil cx o1 _ $$ Hcobj
    rcases cx with ci1 | _
    rotate_left
    · exact absurd rfl Hcn
    (try wp_auto)
    wp_apply (wp_getStateFromObject Obj sp c (GoInterface.ok ci1) o1 r1) $$ [Hcobj] as %st %err Hgs
    · iframe #
      iexact Hcobj
    icases Hgs with (⟨%He, Hos⟩ | #Herr)
    rotate_left
    · ihave %Hne := unkErr_ne c err $$ Herr
      rcases err with ei | _
      rotate_left
      · exact absurd rfl Hne
      gu_ret
      iunfold updOut
      ileft
      isplitr
      · iexact Herr
      iexists o0, rv0
      iexact Hout
    subst He
    (try wp_auto)
    wp_apply wp_AddEvent spn _ _ $$ []
    · iframe #
      ipureintro; exact Hspn
    (try wp_auto)
    obtain ⟨hD1rv, hD1f⟩ := hD1 o1 r1 rfl
    ihave HI : (∃ (st : Loc) (s : OState Obj),
        "origState" ∷ origState_ptr ↦ st ∗ "Hos" ∷ ownState c st s ∗
        "Hout" ∷ c.S.objAt (interface.mkOk (go.GoType.PointerType c.S.objTy) #p) o0 rv0 ∗
        "#Hfrom" ∷ stFrom c pk s ∗ "%Hsr" ∷ ⌜(s.rev = W64 0 → ign = true) ∧ szOk c f s⌝ ∗
        "Hph" ∷ ((⌜s.current = false ∧ pr.rv = none ∧ ∀ n, f s.o n = f s.o (uint.nat s.rev)⌝ ∗
              W ∗ £ 1 ∗ dghostVar γc (DFrac.own 1) (none : Option KVState) ∗
              dghostVar γt (DFrac.own 1) () ∗
              dghostVar γp (DFrac.own 1) (none : Option (w64 × w64))) ∨
            (∃ σ : KVState, rdFacts c σ ∗ ⌜rdOf c pk ign σ s⌝ ∗
              (if stepHand c STEP σ then iprop(∃ σ1, Φu σ1 ∗
                ⌜(c.abs σ1).items pk = (c.abs σ).items pk ∧ σ1.rev = σ.rev⌝) else W))) :
        IProp GF) $$ [origState Hos HW Hlc1 Hc Htok Hp Hout]
    · iexists st, ⟨o1, r1, c.S.encode o1, false, false⟩
      iframe origState Hos Hout
      isplitr
      · unfold stFrom
        iright
        iright
        isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl, Hr1⟩
        iexact Hver1
      isplitr
      · ipureintro
        refine ⟨fun h => absurd h Hr1, ?_⟩
        intro o' hok hw
        exact hcsz o1 r1 o' rfl hok (by simpa using hw)
      ileft
      iframe HW Hlc1 Hc Htok Hp
      ipureintro; exact ⟨rfl, hD1rv, hD1f⟩
    iclear Hver1
    clear Hr1 Hcn st hD1rv hD1f
  all_goals
    wp_for HI
    obtain ⟨hsr0, hsz⟩ := Hsr
    iunfold ownState at Hos
    icases Hos with ⟨%x, %m, %dsl, %Hstn, Hstp, Hobj, #Hdsl, Hm⟩
    (try simp only [decide_eq_true_eq, ↓reduceIte])
    (try wp_auto)
    -- `Preconditions.Check` on the state's object
    ihave #Hmeta' := Hmeta
    iunfold metaOk at Hmeta'
    wp_apply (wp_Check pp pr pk x (c.S.objAt x s.o (c.S.fmtRV s.rev)) (c.S.uid s.o)
        (c.S.fmtRV s.rev)) $$ [Hobj]
    · iframe # Hobj
      iapply Hmeta'
    iintro %e1 ⟨Hobj, Hck⟩
    cases hpok : pr.ok (c.S.uid s.o) (c.S.fmtRV s.rev)
    · isimp only [hpok, Bool.false_eq_true, ↓reduceIte] at Hck
      ihave #Hck0 := Hck
      ihave #Hck' := Hck0
      iunfold invalidErrIs at Hck'
      icases Hck' with ⟨%l, %e2, %Hl, -⟩
      subst Hl
      have hpf : (c.S.preOk pr) s.o (uint.nat s.rev) = false := by
        unfold ObjCodec.preOk; rw [W64_uint_nat]; exact hpok
      have hmod := fun (st0 : KSt Obj) h =>
        update_cur_pre st0 pk ign c.S.zero (c.S.preOk pr) f s.o (uint.nat s.rev) h hpf
      ihave #Hε : □ (∀ o rv, c.S.objAt (interface.mkOk (go.GoType.PointerType c.S.objTy) #p) o rv -∗
          respIs c (KResp.err (KErr.invalidObj pk) : KResp Obj E)
            (interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty) #l)
            (interface.mkOk (go.GoType.PointerType c.S.objTy) #p)) $$ []
      · imodintro
        iintro %o %rv Ho
        simp only [respIs]
        iframe Hck0
        iexists o, rv
        iexact Ho
      ihave Hos : ownState c st s $$ [Hstp Hobj Hm]
      · iunfold ownState
        iexists x, m, dsl
        iframe Hstp Hobj Hdsl Hm
        ipureintro; exact Hstn
      icases (ownState_split c st s) $$ Hos with ⟨%x', Hx, -⟩
      (try wp_auto)
      gu_refresh
    · isimp only [hpok, ↓reduceIte] at Hck
      icases Hck with %He1
      subst He1
      have hpre : (c.S.preOk pr) s.o (uint.nat s.rev) = true := by
        unfold ObjCodec.preOk; rw [W64_uint_nat]; exact hpok
      (try wp_auto)
      ihave Hos : ownState c st s $$ [Hstp Hobj Hm]
      · iunfold ownState
        iexists x, m, dsl
        iframe Hstp Hobj Hdsl Hm
        ipureintro; exact Hstn
      wp_apply wp_updateState Obj E sp c st s f uf $$ [$Hos] as %ret %ttl %uerr ⟨⟨%x', Hx⟩, Hres⟩
      · iframe #
      cases hfr : f s.o (uint.nat s.rev) with
      | error e =>
        isimp only [hfr] at Hres
        icases Hres with %Huerr
        rcases uerr with ei | _
        rotate_left
        · exact absurd rfl Huerr.1
        have hmod := fun (st0 : KSt Obj) h =>
          update_cur_err st0 pk ign c.S.zero (c.S.preOk pr) f s.o (uint.nat s.rev) h hpre e hfr
        ihave #Hε : □ (∀ o rv, c.S.objAt (interface.mkOk (go.GoType.PointerType c.S.objTy) #p) o rv -∗
            respIs c (KResp.err (KErr.user e) : KResp Obj E) (GoInterface.ok ei)
              (interface.mkOk (go.GoType.PointerType c.S.objTy) #p)) $$ []
        · imodintro
          iintro %o %rv Ho
          simp only [respIs]
          isplitr
          · ipureintro; exact Huerr
          iexists o, rv
          iexact Ho
        (try wp_auto)
        gu_refresh
      | ok o' =>
        isimp only [hfr] at Hres
        icases Hres with ⟨%Huerr, Hret⟩
        obtain ⟨rfl, rfl⟩ := Huerr
        (try wp_auto)
        wp_apply wp_AddEvent spn _ _ $$ []
        · iframe #
          ipureintro; exact Hspn
        (try wp_auto)
        ihave #Henc' := Henc
        iunfold encodeOk at Henc'
        wp_apply Henc' $$ [$Hret] as %esl %eerr Hret Hen
        icases Hen with (⟨%Heerr, Hesl⟩ | ⟨%Heerr, #Hes⟩)
        · subst Heerr
          ipersist Hesl
          (try wp_auto)
          wp_apply wp_Int as %kvl -
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %lsl ⟨Hlsl, -⟩
          (try wp_auto)
          wp_apply wp_AddEvent spn _ _ $$ []
          · iframe #
            ipureintro; exact Hspn
          (try wp_auto)
          iunfold ownStateX at Hx
          icases Hx with ⟨%m', %dsl', %Hstn', Hstp, #Hdsl', Hm⟩
          (try wp_auto)
          cases hst : s.stale
          · simp only [Bool.not_false]
            (try wp_auto)
            wp_apply bytes.wp_Equal esl dsl' DFrac.discard DFrac.discard _ _ $$ [] as ⟨-, -⟩
            · iframe #
            cases hq : decide (c.S.encode o' = s.data)
            · -- the encoding differs: the write
              (try simp only [hq])
              have hw : (!s.stale && decide (c.S.encode o' = s.data)) = false := by
                rw [hst, hq]; rfl
              (try wp_auto)
              ihave HW : W $$ [Hph]
              · icases Hph with (⟨-, HW, -⟩ | ⟨%σ, #Hfs, %Hrd, HT⟩)
                · iexact HW
                · have hh := rd_hand_upd c σ pk hpfx s ign Hrd (c.S.preOk pr) f o' hpre hfr hw
                  isimp only [hh, Bool.false_eq_true, ↓reduceIte] at HT
                  iexact HT
              ihave Hx : ownStateX c st s x' $$ [Hstp Hm]
              · iunfold ownStateX
                (try rw [hst])
                iexists m', dsl'
                iframe Hstp Hdsl' Hm
                ipureintro; exact Hstn'
              wp_apply (wp_updateOnce Obj E sp c ci' cd spn pk
                  (interface.mkOk (go.GoType.PointerType c.S.objTy) #p) o0 rv0 st s x' esl v p ign
                  (c.S.preOk pr) f o' W Φu hpfx hkl hpre hfr (hsz o' hfr hw) hw)
                  $$ [$Hx $Hout $HW] as %st' %ok %uerr Hd
              · iframe #
                ipureintro; exact ⟨Hspn, hsr0, Hv⟩
              gu_once
            · -- the encoding is the state's data: the no-op
              have hn : (!s.stale && decide (c.S.encode o' = s.data)) = true := by
                rw [hst, hq]; rfl
              have hqe : c.S.encode o' = s.data := of_decide_eq_true hq
              ihave #Hdec' := Hdec
              iunfold decoderOk at Hdec'
              cases hcur : s.current
              · -- the cached state: the store re-reads the key (the first read)
                (try wp_auto)
                icases Hph with (⟨%HD1, HW, Hlc, Hc, Htok, Hp⟩ | ⟨%σ, -, %Hrd, -⟩)
                rotate_left
                · exact absurd (rdOf_current c pk ign σ s Hrd) (by rw [hcur]; decide)
                ihave %Hcd := stFrom_cached c pk s $$ Hfrom
                obtain ⟨-, hsd, -⟩ := Hcd hcur
                have ho' : o' = s.o := by
                  have h1 := c.S.decode_encode o'
                  rw [hqe, hsd, c.S.decode_encode] at h1
                  exact (Option.some.inj h1).symm
                imod (rwInv_alloc_at γc γt γp c pk (stepHand c STEP) W Φu ⊤) $$ [HW Hc] with #Hrw
                · iframe HW Hc
                ihave Hmk := (rwInv_maker γc γt γp c pk STEP (stepHand c STEP)
                  (handOk_upd c pk ign c.S.zero (c.S.preOk pr) f) W Φu) $$ [Hp]
                · iframe Hrw Hp Hau
                ihave #Hgf' := Hgf
                iunfold getStateOk at Hgf'
                wp_apply Hgf' $$ [Hmk] as %st2 %err2 Hr
                · iexact Hmk
                icases Hr with (#Herr | ⟨%σ, #Hrq, %Hvals, Hat⟩)
                · ihave %Hne := unkErr_ne c err2 $$ Herr
                  rcases err2 with ei | _
                  rotate_left
                  · exact absurd rfl Hne
                  gu_ret
                  iunfold updOut
                  ileft
                  isplitr
                  · iexact Herr
                  iexists o0, rv0
                  iexact Hout
                ihave #Hrq' := Hrq
                iunfold rdQ at Hrq'
                icases Hrq' with ⟨#Hfs, -, -⟩
                imod (rwInv_after γc γt γp c pk STEP (stepHand c STEP)
                  (handOk_upd c pk ign c.S.zero (c.S.preOk pr) f) W Φu σ) $$ [Htok Hrq Hlc] with HT
                · iframe Hrw Htok Hrq Hlc
                ihave Hat := stAt_cases c pk ign σ st2 err2 $$ Hat
                icases Hat with (⟨%Hn, Herr⟩ | ⟨%He, %s2, Hos2, %Hrd⟩)
                · obtain ⟨hf, rfl, rfl⟩ := Hn
                  iunfold storageErrIs at Herr
                  icases Herr with ⟨%ep, %Hep, #Hep⟩
                  subst Hep
                  gu_ret
                  iapply (gu_answer c pk false (c.S.preOk pr) f W Φu σ _ _ _
                    (update_none c σ pk hf c.S.zero (c.S.preOk pr) f))
                  iframe HT
                  simp only [respIs, storageErrIs]
                  isplitl []
                  · iexists ep
                    iframe Hep
                    ipureintro; rfl
                  iexists o0, rv0
                  iexact Hout
                subst He
                (try wp_auto)
                iunfold ownState at Hos2
                icases Hos2 with ⟨%x2, %m2, %dsl2, %Hstn2, Hstp2, Hobj2, #Hdsl2, Hm2⟩
                (try wp_auto)
                wp_apply bytes.wp_Equal esl dsl2 DFrac.discard DFrac.discard _ _ $$ [] as ⟨-, -⟩
                · iframe #
                cases hq2 : decide (c.S.encode o' = s2.data)
                · -- the data changed: the next iteration from the read
                  (try simp only [hq2])
                  (try wp_auto)
                  ihave Hos2 : ownState c st2 s2 $$ [Hstp2 Hobj2 Hm2]
                  · iunfold ownState
                    iexists x2, m2, dsl2
                    iframe Hstp2 Hobj2 Hdsl2 Hm2
                    ipureintro; exact Hstn2
                  ihave Hfr := stFrom_rdOf c pk ign σ s2 Hrd $$ Hfs
                  icases Hfr with ⟨#Hfrom', %Hsr'⟩
                  wp_for_post
                  iframe
                  iexists st2, s2
                  iframe origState Hos2 Hout Hfrom'
                  isplitr
                  · ipureintro; exact ⟨Hsr'.1, rd_szOk c pk ign f σ s2 hfsz hzsz Hrd Hvals⟩
                  iright
                  iexists σ
                  iframe Hfs HT
                  ipureintro; exact Hrd
                · -- the same data: the key holds the cached object (D1: the same answer)
                  have hq2e : c.S.encode o' = s2.data := of_decide_eq_true hq2
                  have hso2 : s2.o = o' := rd_data c pk ign σ s2 Hrd o' hq2e.symm
                  have hpre2 : c.S.preOk pr s2.o (uint.nat s2.rev) = true := by
                    rw [hso2, ho', preOk_rv_none c pr HD1.2.1 s.o (uint.nat s2.rev) (uint.nat s.rev)]
                    exact hpre
                  have hok2 : f s2.o (uint.nat s2.rev) = .ok o' := by
                    have h := HD1.2.2 (uint.nat s2.rev)
                    rw [hso2]
                    conv => lhs; rw [ho']
                    rw [h]
                  (try simp only [hq2])
                  (try wp_auto)
                  cases hst2 : s2.stale
                  · -- not stale: the object read, the model's no-op there
                    have hn2 : (!s2.stale && decide (c.S.encode o' = s2.data)) = true := by
                      rw [hst2, hq2]; rfl
                    have hdec2 : c.S.decode s2.data = some s2.o := by
                      rw [← hq2e, hso2, c.S.decode_encode]
                    (try simp only [Bool.not_false])
                    (try wp_auto)
                    wp_apply Hdec' $$ [$Hdsl2] [$Hout] as %derr Hdres
                    rw [hdec2]
                    icases Hdres with ⟨%Hderr, Hout⟩
                    subst Hderr
                    gu_ret
                    iapply (gu_answer c pk ign (c.S.preOk pr) f W Φu σ _ _ _
                      (rd_noop c pk hpfx ign σ s2 Hrd (c.S.preOk pr) f o' hpre2 hok2 hn2))
                    iframe HT
                    simp only [respIs]
                    rw [W64_uint_nat]
                    iframe Hout
                  · -- stale: the write, from the read
                    have hw2 : (!s2.stale && decide (c.S.encode o' = s2.data)) = false := by
                      rw [hst2]; rfl
                    have hh := rd_hand_upd c σ pk hpfx s2 ign Hrd (c.S.preOk pr) f o' hpre2 hok2 hw2
                    isimp only [hh, Bool.false_eq_true, ↓reduceIte] at HT
                    (try simp only [Bool.not_true])
                    (try wp_auto)
                    ihave Hx2 : ownStateX c st2 s2 x2 $$ [Hstp2 Hm2]
                    · iunfold ownStateX
                      (try rw [hst2])
                      iexists m2, dsl2
                      iframe Hstp2 Hdsl2 Hm2
                      ipureintro; exact Hstn2
                    ihave Hfr := stFrom_rdOf c pk ign σ s2 Hrd $$ Hfs
                    icases Hfr with ⟨#Hfrom2, %Hsr2⟩
                    wp_apply (wp_updateOnce Obj E sp c ci' cd spn pk
                        (interface.mkOk (go.GoType.PointerType c.S.objTy) #p) o0 rv0 st2 s2 x2 esl v p ign
                        (c.S.preOk pr) f o' W Φu hpfx hkl hpre2 hok2
                        (rd_szOk c pk ign f σ s2 hfsz hzsz Hrd Hvals o' hok2 hw2) hw2)
                        $$ [$Hx2 $Hout $HT] as %st' %ok %uerr Hd
                    · iframe #
                      ipureintro; exact ⟨Hspn, Hsr2.1, Hv⟩
                    gu_once
              · -- a read's state: current, the object read, the model's no-op there
                (try simp only [Bool.not_true, Bool.not_false])
                (try wp_auto)
                icases Hph with (⟨%HD1, -⟩ | ⟨%σ, #Hfs, %Hrd, HT⟩)
                · exact absurd HD1.1 (by simp)
                have hso : s.o = o' := rd_data c pk ign σ s Hrd o' hqe.symm
                have hdec : c.S.decode s.data = some s.o := by
                  rw [← hqe, hso, c.S.decode_encode]
                wp_apply Hdec' $$ [$Hdsl'] [$Hout] as %derr Hdres
                rw [hdec]
                icases Hdres with ⟨%Hderr, Hout⟩
                subst Hderr
                gu_ret
                iapply (gu_answer c pk ign (c.S.preOk pr) f W Φu σ _ _ _
                  (rd_noop c pk hpfx ign σ s Hrd (c.S.preOk pr) f o' hpre hfr hn))
                iframe HT
                simp only [respIs]
                rw [W64_uint_nat]
                iframe Hout
          · -- a stale state: the write
            simp only [Bool.not_true]
            have hw : (!s.stale && decide (c.S.encode o' = s.data)) = false := by
              rw [hst]; rfl
            (try wp_auto)
            ihave HW : W $$ [Hph]
            · icases Hph with (⟨-, HW, -⟩ | ⟨%σ, #Hfs, %Hrd, HT⟩)
              · iexact HW
              · have hh := rd_hand_upd c σ pk hpfx s ign Hrd (c.S.preOk pr) f o' hpre hfr hw
                isimp only [hh, Bool.false_eq_true, ↓reduceIte] at HT
                iexact HT
            ihave Hx : ownStateX c st s x' $$ [Hstp Hm]
            · iunfold ownStateX
              (try rw [hst])
              iexists m', dsl'
              iframe Hstp Hdsl' Hm
              ipureintro; exact Hstn'
            wp_apply (wp_updateOnce Obj E sp c ci' cd spn pk
                (interface.mkOk (go.GoType.PointerType c.S.objTy) #p) o0 rv0 st s x' esl v p ign
                (c.S.preOk pr) f o' W Φu hpfx hkl hpre hfr (hsz o' hfr hw) hw)
                $$ [$Hx $Hout $HW] as %st' %ok %uerr Hd
            · iframe #
              ipureintro; exact ⟨Hspn, hsr0, Hv⟩
            gu_once
        · -- the encoding failed
          obtain ⟨Heerr, Hee⟩ := Heerr
          rcases eerr with ee | _
          rotate_left
          · exact absurd rfl Heerr
          (try wp_auto)
          ihave #Hes' := go_etcd_io.etcd.cache.v3.errStrOk_elim ee $$ Hes
          iunfold go_etcd_io.etcd.cache.v3.errorStringSpec at Hes'
          wp_apply wp_Int as %kvl -
          wp_apply Hes' as %estr
          wp_apply wp_String as %kve -
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %esl' ⟨Hesl', -⟩
          (try wp_auto)
          wp_apply wp_AddEvent spn _ _ $$ []
          · iframe #
            ipureintro; exact Hspn
          gu_ret
          iunfold updOut
          ileft
          isplitl []
          · iapply (unkErr_enc c _ (by nofun) Hee)
          iexists o0, rv0
          iexact Hout

end proof

end k8s
end EtcdGrove
end Perennial
