/-
The definitions, specs and lemmas of `RemoveL.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.UpsertLDefs
public import Dsverify.Proof.github_com.orcaman.concurrent_map.IterCbPDefs
@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

set_option linter.unusedSectionVars false

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

/-- The locked shard after `key`'s ghost delete. -/
def CmapLock.del (t : CmapLock) (key : GoString) : CmapLock :=
  { t with Mi := GMap.delete key t.Mi }

/-- A pin at half its fraction (`cmapPin_split`). -/
def PinD.half (π : PinD) : PinD := { π with q := π.q.half }

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]

/-- **The ghost delete** under the write lock: the view loses `key` (bound to `o`, as the token
says), the token follows. -/
theorem cmapLocked_delete (E : CoPset) (hE : (↑cmapN : CoPset) ⊆ E) (γ : GName)
    (key : GoString) (o : Option GoInterface) (t : CmapLock) (M : GMap GoString GoInterface) :
    cmapLocked (GF := GF) γ key o t ∗ cmapView γ M ⊢
      |={E}=> cmapLocked γ key none (t.del key) ∗ cmapView γ (GMap.delete key M) ∗
        ⌜M !! key = o⌝ := by
  obtain ⟨n, shs, p, Mi⟩ := t
  iintro ⟨Hl, Hview⟩
  iunfold cmapLocked at Hl
  icases Hl with ⟨#Hinv, %Hp, Hg⟩
  iinv Hinv with Hi0 Hclose
  iunfold cmapInv at Hi0
  icases Hi0 with ⟨%M0, >Hv, >Hs⟩
  iunfold cmapView at Hview
  icases Hview with ⟨%c, Hview⟩
  icombine Hview Hv gives % ⟨_, Heq⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
  icases BigSepL.bigSepL_lookup_acc_impl Hp.1 $$ Hs with ⟨Hi, Hback⟩
  icombine Hg Hi gives % ⟨_, HeqI⟩
  imod ghostVar_update_halves (GMap.delete key M, (n, shs)) γ (M, (n, shs)) (M, (n, shs))
    $$ Hview Hv with ⟨Hview, Hv⟩
  imod ghostVar_update_halves (GMap.delete key Mi) p.2 Mi _ $$ Hg Hi with ⟨Hg, Hi⟩
  ihave Hs := Hback $$
    %(fun j y => iprop(ghostVar y.2 (1 : Qp).half (shardPart n j (GMap.delete key M)))) [] [Hi]
  · imodintro
    iintro %k %y %_ %hne H
    simp only []
    rw [shardPart_delete, if_neg (Ne.symm hne)]
    iexact H
  · simp only []
    rw [shardPart_delete, if_pos rfl, ← HeqI]
    iexact Hi
  imod Hclose $$ [Hv Hs] with _
  · inext; iunfold cmapInv; iexists (GMap.delete key M); iframe Hv Hs
  imodintro
  isplitl [Hg]
  · iunfold cmapLocked
    simp only [CmapLock.del]
    iframe Hinv Hg
    ipureintro
    exact ⟨Hp.1, GMap.lookup_delete Mi key⟩
  isplitl [Hview]
  · iunfold cmapView; iexists _; iexact Hview
  ipureintro
  rw [← lookup_shardPart_same n M key, ← HeqI, Hp.2]

/-- A pin splits in halves (`π.half`). -/
theorem cmapPin_split (γ : GName) (k : GoString) (v : GoInterface) (π : PinD) :
    cmapPin (GF := GF) γ k v π ⊣⊢ cmapPin γ k v π.half ∗ cmapPin γ k v π.half := by
  obtain ⟨n, shs, i, p, q, Mi⟩ := π
  constructor
  · iintro H
    iunfold cmapPin at H
    icases H with ⟨#Hinv, Hg, %Hp⟩
    icases (ghostVar_split_half (GF := GF) p.2 q Mi).1 $$ Hg with ⟨G1, G2⟩
    isplitl [G1]
    · iunfold cmapPin; simp only [PinD.half]; iframe Hinv G1; ipureintro; exact Hp
    · iunfold cmapPin; simp only [PinD.half]; iframe Hinv G2; ipureintro; exact Hp
  · iintro ⟨H1, H2⟩
    iunfold cmapPin at H1 H2
    simp only [PinD.half]
    icases H1 with ⟨#Hinv, G1, %Hp⟩
    icases H2 with ⟨-, G2, -⟩
    iunfold cmapPin
    iframe Hinv
    isplitl [G1 G2]
    · iapply (ghostVar_split_half (GF := GF) p.2 q Mi).2
      iframe G1 G2
    ipureintro; exact Hp

/-- **A write-locked shard is not read-locked**: the lock token on `key` and a pin on `key`
(any fraction) cannot both be held, given the client's view (which identifies the two
invariants). -/
theorem cmapLocked_pin_false (E : CoPset) (hE : (↑cmapN : CoPset) ⊆ E) (γ : GName)
    (key : GoString) (o : Option GoInterface) (t : CmapLock) (v : GoInterface) (π : PinD)
    (M : GMap GoString GoInterface) :
    cmapLocked (GF := GF) γ key o t ∗ cmapPin γ key v π ∗ cmapView γ M ⊢ |={E}=> False := by
  obtain ⟨n, shs, p, Mi⟩ := t
  obtain ⟨n', shs', i', p', q', Mi'⟩ := π
  iintro ⟨Hl, Hpin, Hview⟩
  iunfold cmapLocked at Hl
  icases Hl with ⟨#Hinv, %Hp, Hg⟩
  iunfold cmapPin at Hpin
  icases Hpin with ⟨#Hinv', Hg', %Hp'⟩
  iunfold cmapView at Hview
  icases Hview with ⟨%c, Hview⟩
  -- the pin's invariant: the view's core is the pin's, and the pin's shard is `key`'s
  iinv Hinv' with Hi0 Hclose
  iunfold cmapInv at Hi0
  icases Hi0 with ⟨%M0, >Hv, >Hs⟩
  icombine Hview Hv gives % ⟨_, Heq⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
  icases (BigSepL.bigSepL_lookup_acc Hp'.1).1 $$ Hs with ⟨Hi, Hback⟩
  icombine Hg' Hi gives % ⟨_, HeqI⟩
  ihave Hs := Hback $$ %p' Hi
  rw [list_set_lookup_self _ _ _ Hp'.1]
  imod Hclose $$ [Hv Hs] with _
  · inext; iunfold cmapInv; iexists M; iframe Hv Hs
  have hi : shardOf n' key = i' := by
    have h := Hp'.2
    rw [HeqI, lookup_shardPart] at h
    split at h
    · assumption
    · cases h
  -- the lock's invariant: the view's core is the token's, so the shard is the same
  iinv Hinv with Hi1 Hclose
  iunfold cmapInv at Hi1
  icases Hi1 with ⟨%M1, >Hv, >Hs⟩
  icombine Hview Hv gives % ⟨_, Heq⟩
  obtain ⟨-, hc⟩ := Prod.mk.inj Heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  have hpp : p' = p := by
    have h1 := Hp'.1
    rw [← hi, Hp.1] at h1
    exact (Option.some.inj h1).symm
  subst hpp
  icases (BigSepL.bigSepL_lookup_acc Hp.1).1 $$ Hs with ⟨Hi, -⟩
  icombine Hg Hi gives % ⟨_, HeqJ⟩
  change Mi = shardPart n' (shardOf n' key) M1 at HeqJ
  subst HeqJ
  icombine Hg Hi as H
  icombine H Hg' gives % ⟨Hq, _⟩
  exfalso
  change 1 + q' ≤ 1 at Hq
  simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hq
  have : (0 : Rat) < q'.val := q'.2
  grind

/-- **Two write-lock tokens of one key exclude each other** (round 37b, sv-swb; swift table rev 8c
§3.17, GAP-37a's T16a: a retiring goroutine's `RemoveL` refutes a lock holder's deposited token):
the two tokens' halves and the invariant's half of the shard's ghost variable add up to more
than 1. The view identifies the two invariants, as in `cmapLocked_pin_false`. -/
theorem cmapLocked_excl (E : CoPset) (hE : (↑cmapN : CoPset) ⊆ E) (γ : GName)
    (key : GoString) (o o' : Option GoInterface) (t t' : CmapLock)
    (M : GMap GoString GoInterface) :
    cmapLocked (GF := GF) γ key o t ∗ cmapLocked γ key o' t' ∗ cmapView γ M ⊢ |={E}=> False := by
  obtain ⟨n, shs, p, Mi⟩ := t
  obtain ⟨n', shs', p', Mi'⟩ := t'
  iintro ⟨Hl, Hl', Hview⟩
  iunfold cmapLocked at Hl Hl'
  icases Hl with ⟨#Hinv, %Hp, Hg⟩
  icases Hl' with ⟨#Hinv', %Hp', Hg'⟩
  iunfold cmapView at Hview
  icases Hview with ⟨%c, Hview⟩
  -- the second token's invariant: the view's core is its
  iinv Hinv' with Hi0 Hclose
  iunfold cmapInv at Hi0
  icases Hi0 with ⟨%M0, >Hv, >Hs⟩
  icombine Hview Hv gives % ⟨_, Heq⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
  imod Hclose $$ [Hv Hs] with _
  · inext; iunfold cmapInv; iexists M; iframe Hv Hs
  -- the first token's invariant: the same core, so the same shard
  iinv Hinv with Hi1 Hclose
  iunfold cmapInv at Hi1
  icases Hi1 with ⟨%M1, >Hv, >Hs⟩
  icombine Hview Hv gives % ⟨_, Heq⟩
  obtain ⟨-, hc⟩ := Prod.mk.inj Heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  have hpp : p' = p := by
    have h1 := Hp'.1
    rw [Hp.1] at h1
    exact (Option.some.inj h1).symm
  subst hpp
  icases (BigSepL.bigSepL_lookup_acc Hp.1).1 $$ Hs with ⟨Hi, -⟩
  icombine Hg Hg' as H
  icombine H Hi gives % ⟨Hq, _⟩
  exfalso
  simp only [Qp.le_iff, Qp.val_add, Qp.val_one, Qp.val_half] at Hq
  grind

end laws

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

/-- `m.Remove(key)` with the shard lock exposed (see the file header): while `key`'s shard is
write-locked, the client's step runs at `⊤` with a later credit and the lock token
`cmapLocked γ key o t` (`o` is `key`'s binding); it must return the token of the deleted binding,
`cmapLocked γ key none (t.del key)` (from `cmapLocked_delete`, which also removes `key` from the
client's view), and gives `Q`, the post. -/
abbrev ConcurrentMap.RemoveL.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (key : GoString)
    (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMapV m γ R ∗
      (∀ (o : Option GoInterface) (t : CmapLock), £ 1 -∗ cmapLocked γ key o t -∗
        |={⊤}=> cmapLocked γ key none (t.del key) ∗ Q) }}
    (App (Val #(methods ConcurrentMap.ty go!"Remove" #m)) (Val #key))
  {{ RET #(); Q }}

set_option goose.wp.extras true

end spec

end Perennial.github_com.orcaman.concurrent_map
