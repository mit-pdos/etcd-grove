/-
Lean-first (no Rocq counterpart).

# k8setcd3: the seeded store (stage 6g)

`Main` seeds the keys `a` and `b` with value `x` in the older encoding (`seedOne`: a client `Put`
of `encodeWith tagV0 k "x"` at the store key, D30g) on a new member's start state (no key, at
revision `1`). The pure part: the two puts' states (`σs2`, explicit: `a` at revision 2, `b` at 3)
and the driver's seeded store (`g0`), related as the instance's invariant takes them (`kvWf`,
`KRel`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.InvSteps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI k8s go_etcd_io.etcd.server.v3.etcdserver
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore)

section pure
variable [ext : FfiSyntax]

/-- A seed key's stored value: its object, value `x`, in the older encoding. -/
def v0 (k : GoString) : GoString := encodeWith tagV0 k go!"x"

/-- `seedOne`'s put of the key `k`. -/
def seedOp (k : GoString) : KVOp := .put (linkv.putOp (mkeyL k) (v0 k))

/-- A new member's start state: no key, at revision `1`. -/
def σb : KVState := { kvs := [], rev := 1 }

/-- The seeded key-values. -/
def kvA : EtcdKv := ⟨mkeyL go!"a", W64 2, W64 2, W64 1, v0 go!"a", W64 0⟩
def kvB : EtcdKv := ⟨mkeyL go!"b", W64 3, W64 3, W64 1, v0 go!"b", W64 0⟩

/-- After the seeds. -/
def σs1 : KVState := { kvs := [kvA], rev := 2 }
def σs2 : KVState := { kvs := [kvA, kvB], rev := 3 }

theorem seed_step1 : kvOpStep (seedOp go!"a") σb = σs1 := by
  rfl

theorem seed_step2 : kvOpStep (seedOp go!"b") σs1 = σs2 := by
  rfl

/-- The driver's seeded items (`seedOne`'s). -/
def itA : item := ⟨go!"a", ⟨go!"a", go!"x", W64 2⟩, false⟩
def itB : item := ⟨go!"b", ⟨go!"b", go!"x", W64 3⟩, false⟩

/-- **The driver's seeded store** (`seed`'s result). -/
def g0s : GSt := ⟨setItemL (setItemL [] itA) itB, W64 3⟩

theorem g0s_items : g0s.items = [itA, itB] := by rfl

end pure

section rel
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The seeded state is the driver's seeded store**, through the store's model. -/
theorem seed_krel (c : StoreCfg GF DObj) (hc : c.S = driverSpec)
    (hp : c.pfx = go!"/registry/objs") : KRel (c.abs σs2) g0s := by
  refine ⟨?_, rfl, by rw [abs_rv]; simp [σs2], ?_⟩
  · rw [g0s_items]; simp only [SortedI, itA, itB, List.map]; decide
  · intro n
    simp only [StoreCfg.abs, hc, hp]
    by_cases ha : n = go!"a"
    · subst ha
      exact ⟨rfl, rfl, rfl⟩
    by_cases hb : n = go!"b"
    · subst hb
      exact ⟨rfl, rfl, rfl⟩
    have ea : ¬ mkeyL go!"a" = mkeyL n := fun h => ha (mkeyL_inj h).symm
    have eb : ¬ mkeyL go!"b" = mkeyL n := fun h => hb (mkeyL_inj h).symm
    have h1 : linkv.absM σs2.kvs (mkeyL n) = none := by
      simp [linkv.absM, mvcc.findKey, σs2, kvA, kvB, ea, eb]
    have h2 : lookupL g0s.items n = (zItem, false) := by
      rw [g0s_items]
      simp [lookupL, itA, itB, Ne.symm ha, Ne.symm hb]
    simp only [linkv.absSt, absK, h1, Option.bind_none, h2, ite_self]
    trivial

/-- **The seeded state is the store's.** -/
theorem seed_wf (c : StoreCfg GF DObj) (hc : c.S = driverSpec)
    (hp : c.pfx = go!"/registry/objs") : kvWf c σs2 := by
  have hfind : ∀ k x, linkv.absM σs2.kvs k = some x → x = linkv.absVR kvA ∨ x = linkv.absVR kvB := by
    intro k x hx
    simp only [linkv.absM, mvcc.findKey, σs2] at hx
    by_cases e1 : kvA.key = k
    · simp [e1] at hx; exact Or.inl hx.symm
    by_cases e2 : kvB.key = k
    · simp [e1, e2] at hx; exact Or.inr hx.symm
    · simp [e1, e2] at hx
  refine ⟨by simp only [σs2]; decide, ?_, ?_, by simp [linkv.absSt, σs2]⟩
  · intro k x _ hx
    rw [hc]
    rcases hfind k x hx with rfl | rfl <;> rfl
  · intro k x hx
    rcases hfind k x hx with rfl | rfl <;> simp [linkv.absVR, kvA, kvB, linkv.absSt, σs2]

end rel

/-! ## The seeding's ghost state -/

/-- No fraction added to `1` is valid. -/
theorem qp_one_add (q : Qp) (h : (1 : Qp) + q ≤ 1) : False := by
  have h1 : (1 : Rat) + q.val ≤ 1 := h
  have := q.2
  grind

section ghost
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris.ProofMode

/-- The seeding's namespace. -/
def seedN : Namespace := nroot .@ ("k8setcd3_seed" : String)

theorem seedN_mask : (↑seedN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩,
    fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩

/-- **The seeding's invariant**: etcd's state, its value half-shared with `Main` (the seed puts'
updates carry `Main`'s half), until `Main` cancels it with its half (then the variable is whole
here, and no update can fire: `seed_au`). -/
def seedInv (γs : GName) (γk : KVNames) : IProp GF :=
  inv seedN iprop((∃ σ : KVState, etcdKV γk σ ∗ ghostVar γs (1 : Qp).half σ) ∨
    (∃ σ : KVState, ghostVar γs 1 σ))

instance seedInv_persistent (γs : GName) (γk : KVNames) : Persistent (seedInv (GF := GF) γs γk) := by
  unfold seedInv; infer_instance

theorem seedInv_alloc (γk : KVNames) (σ : KVState) (E : CoPset) :
    etcdKV (GF := GF) γk σ ⊢ |={E}=> ∃ γs, seedInv γs γk ∗ ghostVar γs (1 : Qp).half σ := by
  iintro Hσ
  imod ghostVar_alloc (GF := GF) σ with ⟨%γs, Hs⟩
  icases (ghostVar_split_half γs 1 σ).1 $$ Hs with ⟨Hs1, Hs2⟩
  imod inv_alloc seedN E (iprop((∃ σ : KVState, etcdKV γk σ ∗ ghostVar γs (1 : Qp).half σ) ∨
      (∃ σ : KVState, ghostVar γs 1 σ)) : IProp GF) $$ [Hσ Hs1] with #Hi
  · inext
    ileft
    iexists σ
    iframe
  imodintro
  iexists γs
  iframe Hs2
  iunfold seedInv
  iexact Hi

/-- **A seed put's update** (fired at most once): at its firing etcd's state is `Main`'s view
`σ`; it moves both halves to the put's next state. -/
theorem seed_au (γs : GName) (γk : KVNames) (op : KVOp) (σ : KVState) (hw : γk.wl.writes op) :
    seedInv γs γk ∗ ghostVar γs (1 : Qp).half σ ⊢
      kvOpAu1 (GF := GF) γk op
        (fun σ' => iprop(ghostVar γs (1 : Qp).half (kvOpStep op σ) ∗ ⌜σ' = σ⌝)) := by
  have Hm := seedN_mask
  iintro ⟨#Hinv, Hs⟩
  unfold kvOpAu1 kvAu1
  isplitr
  · ipureintro; exact hw
  iauintro
  unfold atomic_acc
  iunfold seedInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with (⟨%σ', Hσ, Hs'⟩ | ⟨%σ', Hfull⟩)
  · ihave %Heq := ghostVar_agree γs σ' (1 : Qp).half σ (1 : Qp).half $$ Hs' Hs
    subst Heq
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑seedN from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists σ'
    iframe Hσ
    isplit
    · iintro Hσ
      imod Hclose2 with -
      imod Hclose $$ [Hσ Hs'] with -
      · inext
        ileft
        iexists σ'
        iframe
      imodintro
      iexact Hs
    · iintro Hσ
      imod Hclose2 with -
      imod ghostVar_update_halves (kvOpStep op σ') γs σ' σ' $$ Hs' Hs with ⟨Hs', Hs⟩
      imod Hclose $$ [Hσ Hs'] with -
      · inext
        ileft
        iexists _
        iframe
      imodintro
      iframe Hs
      ipureintro; rfl
  · ihave %Hbad := ghostVar_valid_2 γs σ' 1 σ (1 : Qp).half $$ Hfull Hs
    exact (qp_one_add _ Hbad.1).elim

/-- **The seeding's end**: `Main` hands its half in for etcd's state. -/
theorem seedInv_cancel (γs : GName) (γk : KVNames) (σ : KVState) :
    seedInv γs γk ∗ ghostVar γs (1 : Qp).half σ ⊢ |={⊤}=> etcdKV (GF := GF) γk σ := by
  iintro ⟨#Hinv, Hs⟩
  iunfold seedInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with (⟨%σ', Hσ, Hs'⟩ | ⟨%σ', Hfull⟩)
  · ihave %Heq := ghostVar_agree γs σ' (1 : Qp).half σ (1 : Qp).half $$ Hs' Hs
    subst Heq
    ihave Hfull := (ghostVar_split_half γs 1 σ').2 $$ [Hs' Hs]
    · iframe
    imod Hclose $$ [Hfull] with -
    · inext
      iright
      iexists σ'
      iexact Hfull
    imodintro
    iexact Hσ
  · ihave %Hbad := ghostVar_valid_2 γs σ' 1 σ (1 : Qp).half $$ Hfull Hs
    exact (qp_one_add _ Hbad.1).elim

/-- **The store's history at the seeded state**: its two key-values. -/
theorem histAuth_seed :
    ⊢ |==> ∃ γh, histAuth (GF := GF) γh σs2 := by
  imod ghost_map_alloc_empty (GF := GF) (K := GoString × w64) (V := GoString) with ⟨%γh, HA⟩
  imod ghost_map_insert_persist (kvA.key, kvA.modRev) kvA.value rfl $$ HA with ⟨HA, #Ha⟩
  imod ghost_map_insert_persist (kvB.key, kvB.modRev) kvB.value (by rfl) $$ HA with ⟨HA, #Hb⟩
  imodintro
  iexists γh
  iunfold histAuth
  iexists _
  iframe HA
  isplitr
  · ipureintro
    intro k r v hv
    by_cases e2 : (kvB.key, kvB.modRev) = (k, r)
    · simp only [Prod.mk.injEq] at e2; obtain ⟨-, rfl⟩ := e2; decide
    rw [GMap.lookup_insert_ne _ _ e2] at hv
    by_cases e1 : (kvA.key, kvA.modRev) = (k, r)
    · simp only [Prod.mk.injEq] at e1; obtain ⟨-, rfl⟩ := e1; decide
    rw [GMap.lookup_insert_ne _ _ e1] at hv
    cases hv
  iunfold kvSeen
  imodintro
  iintro %v %hv
  simp only [σs2, List.mem_cons, List.not_mem_nil, _root_.or_false] at hv
  rcases hv with rfl | rfl
  · iexact Ha
  · iexact Hb

/-- **The instance's invariant at the seeded state**, and the library's initial state. -/
theorem kInv_seed (γk : KVNames) (c : StoreCfg GF DObj) (hc : c.S = driverSpec)
    (hp : c.pfx = go!"/registry/objs") (hW : ∀ op, γk.wl.writes op) (E : CoPset) :
    etcdKV (GF := GF) γk σs2 ∗ histAuth c.γh σs2 ⊢
      |={E}=> ∃ γ : KNames, kInv γ c g0s γk ∗ kState γ g0s (linkv.pInit (kSpec g0s)) := by
  iintro ⟨Hσ, Hhist⟩
  imod ghostVar_alloc (GF := GF) ([] : List OpV) with ⟨%γh, Hh⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Input) with ⟨%γp, Hp⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := KVState) with ⟨%γr, Hr⟩
  imod ghost_map_insert_persist σs2.rev σs2 rfl $$ Hr with ⟨Hr, #He⟩
  icases (ghostVar_split_half γh 1 ([] : List OpV)).1 $$ Hh with ⟨Hh1, Hh2⟩
  imod inv_alloc drvInvN E (kInvBody (GF := GF) ⟨γh, γp, γr⟩ c g0s γk) $$ [Hh1 Hσ Hp Hr Hhist]
    with #Hinv
  · inext
    iunfold kInvBody
    iexists [], linkv.pInit (kSpec g0s), σs2, ∅, 0
    iframe
    isplitl
    · iunfold revOwn
      iexists _
      iframe He Hr
      ipureintro
      exact ⟨GMap.lookup_insert _ _ _, fun n hn => by
        rw [GMap.lookup_insert_ne _ _ (by omega)]; rfl⟩
    ipureintro
    exact ⟨rfl, kOk_init σs2 (seed_wf c hc hp) (by decide) (seed_krel c hc hp)⟩
  imodintro
  iexists ⟨γh, γp, γr⟩
  iunfold kInv
  iframe Hinv
  isplitr
  · ipureintro; exact hW
  iunfold kState
  iexists []
  iframe
  ipureintro; rfl

end ghost

end k8setcd3
end EtcdGrove
end Perennial
