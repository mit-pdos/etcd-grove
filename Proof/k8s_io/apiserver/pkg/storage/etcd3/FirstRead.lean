/-
Lean-first (no Rocq counterpart).

# The store's first read: the caller's token handed once, at the response's state (D30n)

`Delete` and `GuaranteedUpdate` read the key (`getCurrentState`, through `kubernetes.Client.Get`)
before deciding whether to write. The read's update is persistent (the client fires it at many
states, the response reflecting one), and `Get` prophesies its response's pair (`rdPair`: its
revision and the key's mod revision), so the update knows, at each state, whether it is the
response's. `rwInv` lets the store hand the caller's token `W` (`k8sAuRW`'s linearization point,
D30n) at the first state with the response's pair where the step is the identity (`hand`): there
the answer is read-like, and the store answers from that state (`rdPair_items`: two states seen in
the history with the same pair have the same item), so it never writes after.

- `rwInv γc γt γp c key hand W Φ` (at `k8sN`): `W` (and the commit bit `γc` at `none`); or, once
  handed at `σ`, `γc` read-only at `σ` and the caller's result `Φ σ` (until the store takes it,
  with `γt`); or, once the store took `W` back (the response's state does not hand), `γt` and that
  state. `γp` holds the pair the read was made for (`Get` makes it once).
- `rdQ`: what a firing at `σ` answers: its facts, the pair, and, if `σ` has the pair and hands,
  the state it was handed at.
- `rwInv_maker`: the single-use maker `Get` takes (`∀ R m, |==> □ …`), from the caller's updates;
  `rwInv_fired`/`rwInv_unfired`: after the response, its result `Φ σ₁` or `W` back.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Updates
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__Get

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [ext : FfiSyntax]

/-- A read's pair at `σ`: its revision and the key's mod revision (`0` if absent). -/
def rdPair (key : GoString) (σ : KVState) : w64 × w64 := (W64 (σ.rev : Int), kubernetes.modAt key σ)

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj]

instance kvSeen_timeless (γh : GName) (σ : KVState) : Timeless (kvSeen (GF := GF) γh σ) := by
  unfold kvSeen; infer_instance

instance rdFacts_timeless (c : StoreCfg GF Obj) (σ : KVState) : Timeless (rdFacts c σ) := by
  unfold rdFacts; infer_instance

/-- **When the store may hand the token at a read**: the step is the identity there, and whether
it hands depends only on the key's item and the revision. -/
structure HandOk (c : StoreCfg GF Obj) (key : GoString) (step : KSt Obj → KSt Obj)
    (hand : KVState → Bool) : Prop where
  id : ∀ σ, kvWf c σ → hand σ = true → step (c.abs σ) = c.abs σ
  loc : ∀ σ1 σ2, (c.abs σ1).items key = (c.abs σ2).items key → σ1.rev = σ2.rev →
    hand σ1 = hand σ2

/-- Two states of the store with the key's mod revision and the same value there (when present)
have the same item. -/
theorem abs_items_eq (c : StoreCfg GF Obj) (key : GoString) (σ1 σ2 : KVState)
    (hw1 : kvWf c σ1) (hw2 : kvWf c σ2) (hm : kubernetes.modAt key σ1 = kubernetes.modAt key σ2)
    (hv : ∀ v1 v2, mvcc.findKey key σ1.kvs = some v1 → mvcc.findKey key σ2.kvs = some v2 →
      v1.value = v2.value) :
    (c.abs σ1).items key = (c.abs σ2).items key := by
  have hpos : ∀ (σ : KVState), kvWf c σ → ∀ v, mvcc.findKey key σ.kvs = some v →
      0 < uint.nat v.modRev := by
    intro σ hw v hv
    have := (hw.2.2.1 key (linkv.absVR v) (by simp [linkv.absSt, linkv.absM, hv])).1
    simpa [linkv.absVR] using this
  unfold kubernetes.modAt at hm
  cases h1 : mvcc.findKey key σ1.kvs with
  | none =>
    cases h2 : mvcc.findKey key σ2.kvs with
    | none => simp [StoreCfg.abs, absK, linkv.absSt, linkv.absM, h1, h2]
    | some v2 =>
      rw [h1, h2] at hm
      have := hpos σ2 hw2 v2 h2
      simp only [Option.map_none, Option.getD_none, Option.map_some, Option.getD_some] at hm
      rw [← hm] at this
      exact absurd this (by decide)
  | some v1 =>
    cases h2 : mvcc.findKey key σ2.kvs with
    | none =>
      rw [h1, h2] at hm
      have := hpos σ1 hw1 v1 h1
      simp only [Option.map_none, Option.getD_none, Option.map_some, Option.getD_some] at hm
      rw [hm] at this
      exact absurd this (by decide)
    | some v2 =>
      rw [h1, h2] at hm
      simp only [Option.map_some, Option.getD_some] at hm
      have hval := hv v1 v2 h1 h2
      simp [StoreCfg.abs, absK, linkv.absSt, linkv.absM, h1, h2, itemOf, linkv.absVR, hm, hval]

/-- A revision below `2^63` is its word's. -/
theorem rev_of_W64 (r1 r2 : Nat) (h1 : r1 < 2 ^ 63) (h2 : r2 < 2 ^ 63)
    (h : W64 (r1 : Int) = W64 (r2 : Int)) : r1 = r2 := by
  have := congrArg BitVec.toNat h
  simp only [W64, BitVec.toNat_ofInt] at this
  omega

/-- **Two states seen in the history with the same pair** have the same item and revision. -/
theorem rdPair_items (c : StoreCfg GF Obj) (key : GoString) (σ1 σ2 : KVState)
    (h : rdPair key σ1 = rdPair key σ2) :
    rdFacts (GF := GF) c σ1 ∗ rdFacts c σ2 ⊢
      ⌜(c.abs σ1).items key = (c.abs σ2).items key ∧ σ1.rev = σ2.rev⌝ := by
  unfold rdFacts
  iintro ⟨⟨%Hw1, #Hs1⟩, ⟨%Hw2, #Hs2⟩⟩
  simp only [rdPair, Prod.mk.injEq] at h
  have hrev : σ1.rev = σ2.rev := rev_of_W64 _ _ (by omega) (by omega) h.1
  ihave %Hv : ⌜∀ v1 v2, mvcc.findKey key σ1.kvs = some v1 → mvcc.findKey key σ2.kvs = some v2 →
      v1.value = v2.value⌝ $$ []
  · iintro %v1 %v2 %Hf1 %Hf2
    have hk1 : v1.key = key := by simpa using List.find?_some Hf1
    have hk2 : v2.key = key := by simpa using List.find?_some Hf2
    have hm : v1.modRev = v2.modRev := by
      have := h.2
      simp [kubernetes.modAt, Hf1, Hf2] at this
      exact this
    iapply kvSeen_agree c.γh σ1 σ2 v1 v2 (List.mem_of_find?_eq_some Hf1)
      (List.mem_of_find?_eq_some Hf2) (hk1.trans hk2.symm) hm
    iframe Hs1 Hs2
  ipureintro
  exact ⟨abs_items_eq c key σ1 σ2 Hw1.1 Hw2.1 h.2 Hv, hrev⟩

/-- The first read's invariant's contents (see the file header). -/
def rwBody (γc γt γp : GName) (c : StoreCfg GF Obj) (key : GoString) (hand : KVState → Bool)
    (W : IProp GF) (Φ : KVState → IProp GF) : IProp GF :=
  iprop((W ∗ dghostVar γc (DFrac.own 1) (none : Option KVState)) ∨
    (∃ (σ : KVState) (R m : w64), dghostVar γc DFrac.discard (some σ) ∗
      dghostVar γp DFrac.discard (some (R, m)) ∗ ⌜rdPair key σ = (R, m) ∧ hand σ = true⌝ ∗
      rdFacts c σ ∗ (Φ σ ∨ dghostVar γt (DFrac.own 1) ())) ∨
    (∃ (σ : KVState) (R m : w64), dghostVar γt (DFrac.own 1) () ∗
      dghostVar γp DFrac.discard (some (R, m)) ∗ ⌜rdPair key σ = (R, m) ∧ hand σ = false⌝ ∗
      rdFacts c σ))

/-- **The store's first read's invariant** (see the file header). -/
def rwInv (γc γt γp : GName) (c : StoreCfg GF Obj) (key : GoString) (hand : KVState → Bool)
    (W : IProp GF) (Φ : KVState → IProp GF) : IProp GF :=
  inv k8sN (rwBody γc γt γp c key hand W Φ)

instance rwInv_persistent (γc γt γp : GName) (c : StoreCfg GF Obj) (key : GoString)
    (hand : KVState → Bool) (W : IProp GF) (Φ : KVState → IProp GF) :
    Persistent (rwInv γc γt γp c key hand W Φ) := by
  unfold rwInv; infer_instance

/-- **What a firing at `σ` answers** (see the file header). -/
def rdQ (γc γp : GName) (c : StoreCfg GF Obj) (key : GoString) (hand : KVState → Bool)
    (R m : w64) (σ : KVState) : IProp GF :=
  iprop(rdFacts c σ ∗ dghostVar γp DFrac.discard (some (R, m)) ∗
    (⌜rdPair key σ = (R, m) ∧ hand σ = true⌝ → ∃ σ1 : KVState,
      dghostVar γc DFrac.discard (some σ1) ∗ ⌜rdPair key σ1 = (R, m) ∧ hand σ1 = true⌝ ∗
      rdFacts c σ1))

instance rdQ_persistent (γc γp : GName) (c : StoreCfg GF Obj) (key : GoString)
    (hand : KVState → Bool) (R m : w64) (σ : KVState) :
    Persistent (rdQ γc γp c key hand R m σ) := by
  unfold rdQ; infer_instance

/-- **The invariant, allocated** with the caller's token. -/
theorem rwInv_alloc (c : StoreCfg GF Obj) (key : GoString) (hand : KVState → Bool)
    (W : IProp GF) (Φ : KVState → IProp GF) (E : CoPset) :
    W ⊢ |={E}=> ∃ γc γt γp : GName, rwInv γc γt γp c key hand W Φ ∗
      dghostVar γt (DFrac.own 1) () ∗ dghostVar γp (DFrac.own 1) (none : Option (w64 × w64)) := by
  iintro HW
  imod dghostVar_alloc (GF := GF) (none : Option KVState) with ⟨%γc, Hc⟩
  imod dghostVar_alloc (GF := GF) () with ⟨%γt, Ht⟩
  imod dghostVar_alloc (GF := GF) (none : Option (w64 × w64)) with ⟨%γp, Hp⟩
  imod inv_alloc k8sN E (rwBody γc γt γp c key hand W Φ) $$ [HW Hc] with #Hi
  · inext
    iunfold rwBody
    ileft
    iframe
  imodintro
  iexists γc, γt, γp
  iframe Ht Hp
  iunfold rwInv
  iexact Hi

/-- **After the response, at a state that hands**: the caller's result at the state the token was
handed at (`γt` taken; a later credit for the result's `▷`). -/
theorem rwInv_fired (γc γt γp : GName) (c : StoreCfg GF Obj) (key : GoString)
    (hand : KVState → Bool) (W : IProp GF) (Φ : KVState → IProp GF) (σ1 : KVState) :
    rwInv γc γt γp c key hand W Φ ∗ dghostVar γc DFrac.discard (some σ1) ∗
      dghostVar γt (DFrac.own 1) () ∗ £ 1 ⊢ |={⊤}=> Φ σ1 := by
  iintro ⟨#Hc, #Hv, Htok, Hlc⟩
  iunfold rwInv at Hc
  iinv Hc with Hi Hclose
  iunfold rwBody at Hi
  icases Hi with (⟨-, >Hγc⟩ | ⟨%σ', %R, %m, >#Hv', >#Hp, >%Hf, #Hfacts, Hrest⟩ |
    ⟨%σ', %R, %m, >Ht', -⟩)
  · ihave %Hbad := dghostVar_valid_2 γc _ _ _ _ $$ Hv Hγc
    exfalso
    cases Hbad.2
  · ihave %Hvv := dghostVar_agree γc _ _ _ _ $$ Hv Hv'
    simp only [Option.some.injEq] at Hvv
    subst Hvv
    imod lc_fupd_elim_later $$ Hlc Hrest with Hrest
    icases Hrest with (HΦ | Htok')
    · imod Hclose $$ [Htok] with -
      · inext
        iunfold rwBody
        iright
        ileft
        iexists σ1, R, m
        iframe Hv Hp Hfacts
        isplitr
        · ipureintro; exact Hf
        iright
        iexact Htok
      imodintro
      iexact HΦ
    · ihave %Hbad := dghostVar_valid_2 γt _ _ _ _ $$ Htok Htok'
      exfalso
      have h := DFrac.valid_own_op Hbad.1
      exact absurd h (by decide)
  · ihave %Hbad := dghostVar_valid_2 γt _ _ _ _ $$ Htok Ht'
    exfalso
    have h := DFrac.valid_own_op Hbad.1
    exact absurd h (by decide)

/-- **After the response, at a state that does not hand**: the token back (no state with the
response's pair handed it: they have its item, `HandOk.loc`). -/
theorem rwInv_unfired (γc γt γp : GName) (c : StoreCfg GF Obj) (key : GoString)
    (step : KSt Obj → KSt Obj) (hand : KVState → Bool) (hok : HandOk c key step hand)
    (W : IProp GF) [Timeless W] (Φ : KVState → IProp GF) (σs : KVState) (R m : w64)
    (hpair : rdPair key σs = (R, m)) (hh : hand σs = false) :
    rwInv γc γt γp c key hand W Φ ∗ dghostVar γt (DFrac.own 1) () ∗
      rdQ γc γp c key hand R m σs ∗ £ 1 ⊢ |={⊤}=> W := by
  iintro ⟨#Hc, Htok, #HQ, Hlc⟩
  iunfold rdQ at HQ
  icases HQ with ⟨#Hfs, #Hps, -⟩
  iunfold rwInv at Hc
  iinv Hc with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iunfold rwBody at Hi
  icases Hi with (⟨HW, Hγc⟩ | ⟨%σ1, %R', %m', #Hv1, #Hp', %Hf, #Hf1, -⟩ |
    ⟨%σ', %R', %m', Ht', -⟩)
  · imod Hclose $$ [Htok] with -
    · inext
      iunfold rwBody
      iright
      iright
      iexists σs, R, m
      iframe Htok Hps Hfs
      ipureintro; exact ⟨hpair, hh⟩
    imodintro
    iexact HW
  · ihave %Hpe := dghostVar_agree γp _ _ _ _ $$ Hp' Hps
    simp only [Option.some.injEq] at Hpe
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hpe
    ihave %Hsame := rdPair_items c key σ1 σs (Hf.1.trans hpair.symm) $$ [Hf1 Hfs]
    · iframe Hf1 Hfs
    have := hok.loc σ1 σs Hsame.1 Hsame.2
    rw [Hf.2, hh] at this
    cases this
  · ihave %Hbad := dghostVar_valid_2 γt _ _ _ _ $$ Htok Ht'
    exfalso
    have h := DFrac.valid_own_op Hbad.1
    exact absurd h (by decide)

/-- **A firing of the read at a member** (see the file header): the caller's update fires there as
the linearization point, handing `W`, at the first state with the read's pair that hands, and as
a plain read otherwise; the firing answers `rdQ`. -/
theorem rwInv_readAu (γk : KVNames) (γc γt γp : GName) (c : StoreCfg GF Obj) (key : GoString)
    (step : KSt Obj → KSt Obj) (hand : KVState → Bool) (hok : HandOk c key step hand)
    (W : IProp GF) [Timeless W] (Φ : KVState → IProp GF) (R m : w64) :
    rwInv γc γt γp c key hand W Φ ∗ dghostVar γp DFrac.discard (some (R, m)) ∗
      k8sAuRW γk c step W Φ ⊢ kvReadAu γk (rdQ γc γp c key hand R m) := by
  have h : rwInv γc γt γp c key hand W Φ ∗ dghostVar γp DFrac.discard (some (R, m)) ∗
      k8sAuRW γk c step W Φ ⊢
      AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γk ((fun σ => σ) σ), COMM □ rdQ γc γp c key hand R m σ }> := by
    have Hm := k8sN_mask
    refine (BI.and_intro BI.true_intro .rfl).trans (aupd_intro ?_)
    iintro ⟨-, #Hc, #Hp, #HAU⟩
    unfold atomic_acc
    ihave #Hc' := Hc
    iunfold rwInv at Hc'
    iinv Hc' with Hi Hclose
    ihave #HAUk := HAU
    iunfold k8sAuRW at HAUk
    ihave HAC := aupd_aacc $$ HAUk
    iunfold atomic_acc at HAC
    imod HAC with HAC
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at HAC
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    icases HAC with ⟨%σ, ⟨Hkv, %Hwf, #Hseen⟩, Hcl⟩
    imodintro
    iexists σ
    iframe Hkv
    isplit
    · -- abort: nothing moved
      iintro Hkv
      icases Hcl with ⟨Habort, -⟩
      imod Habort $$ [Hkv] with -
      · iframe Hkv Hseen
        ipureintro; exact Hwf
      imod Hclose $$ Hi with -
      imodintro
      iframe Hc Hp HAU
    · iintro Hkv
      icases Hcl with ⟨-, Hcommit⟩
      ihave #Hfs : rdFacts c σ $$ []
      · unfold rdFacts; iframe Hseen; ipureintro; exact Hwf
      by_cases hm : rdPair key σ = (R, m) ∧ hand σ = true
      · iunfold rwBody at Hi
        icases Hi with (⟨>HW, >Hγc⟩ | ⟨%σ1, %R', %m', >#Hv1, >#Hp', >%Hf, >#Hf1, Hrest⟩ |
          ⟨%σ', %R', %m', >Ht', >#Hp', >%Hf, >#Hf'⟩)
        · -- the token is there: handed here
          ispecialize Hcommit $$ %true %σ
          isimp only [↓reduceIte] at Hcommit
          imod Hcommit $$ [Hkv HW] with HΦ
          · iframe Hkv HW
            ipureintro; exact ⟨Hwf.1, (hok.id σ Hwf.1 hm.2).symm⟩
          imod dghostVar_update (some σ) γc none $$ Hγc with Hγc
          imod dghostVar_persist γc 1 _ $$ Hγc with #Hγc
          imod Hclose $$ [HΦ] with -
          · inext
            iunfold rwBody
            iright
            ileft
            iexists σ, R, m
            iframe Hγc Hp Hfs
            isplitr
            · ipureintro; exact hm
            ileft
            iexact HΦ
          imodintro
          imodintro
          iunfold rdQ
          iframe Hfs Hp
          iintro %_
          iexists σ
          iframe Hγc Hfs
          ipureintro; exact hm
        · -- already handed (at a state with the same pair)
          ispecialize Hcommit $$ %false %σ
          isimp only [Bool.false_eq_true, ↓reduceIte] at Hcommit
          imod Hcommit $$ [Hkv] with -
          · iframe Hkv
          ihave %Hpe := dghostVar_agree γp _ _ _ _ $$ Hp' Hp
          simp only [Option.some.injEq] at Hpe
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hpe
          imod Hclose $$ [Hrest] with -
          · inext
            iunfold rwBody
            iright
            ileft
            iexists σ1, R', m'
            iframe Hv1 Hp Hf1 Hrest
            ipureintro; exact Hf
          imodintro
          imodintro
          iunfold rdQ
          iframe Hfs Hp
          iintro %_
          iexists σ1
          iframe Hv1 Hf1
          ipureintro; exact Hf
        · -- taken back: the response's state does not hand, but it has this state's item
          ihave %Hpe := dghostVar_agree γp _ _ _ _ $$ Hp' Hp
          simp only [Option.some.injEq] at Hpe
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hpe
          ihave %Hsame := rdPair_items c key σ' σ (Hf.1.trans hm.1.symm) $$ [Hf' Hfs]
          · iframe Hf' Hfs
          have := hok.loc σ' σ Hsame.1 Hsame.2
          rw [Hf.2, hm.2] at this
          cases this
      · -- not the response's pair, or no handing: a plain read
        ispecialize Hcommit $$ %false %σ
        isimp only [Bool.false_eq_true, ↓reduceIte] at Hcommit
        imod Hcommit $$ [Hkv] with -
        · iframe Hkv
        imod Hclose $$ Hi with -
        imodintro
        imodintro
        iunfold rdQ
        iframe Hfs Hp
        iintro %hm'
        exact absurd hm' hm
  unfold kvReadAu kvAu
  iintro #H
  imodintro
  ihave H2 := h $$ H
  iexact H2

/-- **The single-use maker** `Get` takes (`Client.Get.spec`): the pair recorded once, then the
read at every member. -/
theorem rwInv_maker (γc γt γp : GName) (c : StoreCfg GF Obj) (key : GoString)
    (step : KSt Obj → KSt Obj) (hand : KVState → Bool) (hok : HandOk c key step hand)
    (W : IProp GF) [Timeless W] (Φ : KVState → IProp GF) :
    rwInv γc γt γp c key hand W Φ ∗ dghostVar γp (DFrac.own 1) (none : Option (w64 × w64)) ∗
      □ ([∗list] x ∈ c.ms, k8sAuRW x.γr.kv c step W Φ) ⊢
      (iprop(∀ R m, |==> □ [∧list] x ∈ c.ms,
        ⌜rdQ γc γp c key hand R m = fun _ => iprop(True)⌝ ∨
          kvReadAu x.γr.kv (rdQ γc γp c key hand R m)) : IProp GF) := by
  iintro ⟨#Hc, Hp, #Haus⟩ %R %m
  imod dghostVar_update (some (R, m)) γp none $$ Hp with Hp
  imod dghostVar_persist γp 1 _ $$ Hp with #Hp
  imodintro
  imodintro
  refine BigAndL.bigAndL_intro fun k x hk => ?_
  have hx : x ∈ c.ms := List.mem_of_getElem? hk
  iintro ⟨⟨#Hc, #Haus⟩, #Hp⟩
  iright
  iapply rwInv_readAu x.γr.kv γc γt γp c key step hand hok W Φ R m
  iframe Hc Hp
  iapply (BigSepL.bigSepL_mem (Φ := fun x : client.SrvAt GF => k8sAuRW x.γr.kv c step W Φ)
    hx) $$ Haus

/-- **After the response at `σ`**: the caller's result at a state with `σ`'s item and revision, if
`σ` hands; else the token back. -/
theorem rwInv_after (γc γt γp : GName) (c : StoreCfg GF Obj) (key : GoString)
    (step : KSt Obj → KSt Obj) (hand : KVState → Bool) (hok : HandOk c key step hand)
    (W : IProp GF) [Timeless W] (Φ : KVState → IProp GF) (σ : KVState) :
    rwInv γc γt γp c key hand W Φ ∗ dghostVar γt (DFrac.own 1) () ∗
      rdQ γc γp c key hand (W64 (σ.rev : Int)) (kubernetes.modAt key σ) σ ∗ £ 1 ⊢
      |={⊤}=> if hand σ then iprop(∃ σ1, Φ σ1 ∗
        ⌜(c.abs σ1).items key = (c.abs σ).items key ∧ σ1.rev = σ.rev⌝) else W := by
  iintro ⟨#Hc, Htok, #HQ, Hlc⟩
  cases hh : hand σ
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iapply rwInv_unfired γc γt γp c key step hand hok W Φ σ (W64 (σ.rev : Int)) (kubernetes.modAt key σ) rfl hh
    iframe Hc Htok HQ Hlc
  · simp only [↓reduceIte]
    ihave #HQ' := HQ
    iunfold rdQ at HQ'
    icases HQ' with ⟨#Hfs, -, #Himp⟩
    have hm : rdPair key σ = (W64 (σ.rev : Int), kubernetes.modAt key σ) ∧ hand σ = true := ⟨rfl, hh⟩
    ihave ⟨%σ1, #Hc1, %Hf1, #Hfs1⟩ := Himp $$ %hm
    imod rwInv_fired γc γt γp c key hand W Φ σ1 $$ [Hc Hc1 Htok Hlc] with HΦ
    · iframe Hc Hc1 Htok Hlc
    ihave %Hsame := rdPair_items c key σ1 σ Hf1.1 $$ [Hfs1 Hfs]
    · iframe Hfs1 Hfs
    imodintro
    iexists σ1
    iframe HΦ
    ipureintro; exact Hsame

end defs

end k8s
end EtcdGrove
end Perennial
