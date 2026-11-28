/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemStoreBase.lean (241f27e).
-/
/-
Shared definitions of the `InmemStore` proofs (redesign R1): the representation of a
`*InmemStore` and its two client views.

* `inmemLogs γs L`: the client's (exclusive) view of the log contents `L : proto.RLog`
  (Raft index `k` at position `k-1`).
* `kvView γs st`: the client's (exclusive) view of the stable-store contents `st : StableAbs`.
* `isInmemStore γs i`: the persistent handle. It holds the guard of the `RWMutex` at field `l`
  (writers: `RWMutex.wp_Lock_guard`) and a quarter thread pool of its reader tokens (readers borrow one
  with their quarter token `rtok tid` for the critical section: `Threads/QPool.lean`), with the lock invariant
  `storeInv γs i` (fractional), and the package facts the methods use.

The lock invariant holds a ghost record `c : Conc` of the concrete state (at the lock's
fraction, so that all fractions agree on it), the physical fields and maps at that fraction,
and the other halves of the two client views (at half the fraction). Its facts:
* the `logs` map has exactly the keys `1..|L|`; the entry at `k` is a pointer with a persistent
  points-to to a `Log` value that `logIs` relates to `L`'s entry at `k` (`logPtr`: a stored
  entry is never written again);
* `lowIndex = (L = [] ? 0 : 1)`, `highIndex = |L|` (contiguity);
* `kvInt` is `st.ints`; `kv` has the keys of `st.bytes`, each value a slice with a persistent
  points-to of `st.bytes`' value.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.iface.Stores
public import Perennial.Proof.sync.Results
public import Dsverify.Proof.github_com.hashicorp.raft.Threads.QPool
public import Perennial.Proof.errors.NewVar
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto

-- (hraft_robust L0) `stableAbs_countable` moved to `iface/Stores.lean`.

/-- The ghost names of an `InmemStore`. -/
structure InmemNames where
  conc : GName
  log : GName
  kv : GName

/-- The concrete state recorded in the lock invariant: the log contents `L` (stage 3: a partial map
with the last index written, `LogAbs`), the `lowIndex` field `lo` (stage 3), the stable contents
`st`, the three map references and the contents of the `logs` and `kv` maps (the `kvInt` map's
contents are `st.ints`; `highIndex` is `L.hi`). -/
structure Conc where
  L : LogAbs
  lo : w64
  st : StableAbs
  mlog : Loc
  mkv : Loc
  mint : Loc
  lm : GMap w64 Loc
  kvm : GMap GoString GoSlice

instance conc_countable : Pos.Countable Conc :=
  Pos.Countable.ofInjective
    (fun c => Pos.Countable.encode (c.L, c.lo, c.st, c.mlog, c.mkv, c.mint, c.lm, c.kvm))
    (by
      intro a b h
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h0, h2, h3, h4, h5, h6, h7⟩ := h
      subst h1; subst h0; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7; rfl)

/-- `lowIndex` for the contents `L`. -/
def lowOf (L : RLog) : w64 := if L = [] then W64 0 else W64 1

/-- The pure facts of the concrete state (stage 3: the `logs` map's keys are the partial map's). -/
def concOk (c : Conc) : Prop :=
  (∀ k, (c.L.m.lookup k).isSome → k < 2 ^ 64) ∧
  (∀ k : w64, (c.lm !! k).isSome ↔ (c.L.m.lookup (uint.nat k)).isSome) ∧
  (∀ k : GoString, (c.kvm !! k).isSome ↔ (c.st.bytes !! k).isSome)

theorem ent_none_of_not_mem (L : RLog) (k : Nat) (h : ¬(1 ≤ k ∧ k ≤ L.length)) :
    ent L k = none := by
  unfold ent
  split
  · rfl
  · exact List.getElem?_eq_none (by omega)

/-- The namespace of the reader-token pool. -/
def inmemPoolN : Namespace := nroot.@"inmemstore"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- The persistent facts of the concrete state: each stored log pointer is a `logPtr` of the
entry of `L` at its key; each stored byte slice is a read-only slice of `st.bytes`' value. -/
def concPers (c : Conc) : IProp GF :=
  iprop("#Hplogs" ∷ □ (∀ (k : w64) (p : Loc), ⌜c.lm !! k = some p⌝ -∗
          ∃ e, ⌜c.L.m.lookup (uint.nat k) = some e⌝ ∗ logPtr p (uint.nat k) e) ∗
        "#Hpkv" ∷ □ (∀ (k : GoString) (s : GoSlice), ⌜c.kvm !! k = some s⌝ -∗
          ∃ vb, ⌜c.st.bytes !! k = some vb⌝ ∗ s ↦*□ vb))

instance concPers_persistent (c : Conc) : Persistent (concPers (GF := GF) c) := by
  unfold concPers; infer_instance

/-- The lock invariant's contents at fraction `q`, for the concrete state `c`. -/
def storeBody (γs : InmemNames) (i : Loc) (c : Conc) (q : Qp) : IProp GF :=
  iprop(i.[InmemStore, go!"lowIndex"] ↦{DFrac.own q} c.lo ∗
    i.[InmemStore, go!"highIndex"] ↦{DFrac.own q} c.L.hi ∗
    i.[InmemStore, go!"logs"] ↦{DFrac.own q} c.mlog ∗
    c.mlog ↦${DFrac.own q} c.lm ∗
    i.[InmemStore, go!"kv"] ↦{DFrac.own q} c.mkv ∗
    c.mkv ↦${DFrac.own q} c.kvm ∗
    i.[InmemStore, go!"kvInt"] ↦{DFrac.own q} c.mint ∗
    c.mint ↦${DFrac.own q} c.st.ints ∗
    ghostVar γs.log q.half c.L ∗
    ghostVar γs.kv q.half c.st ∗
    ⌜concOk c⌝ ∗ concPers c)

/-- The lock invariant (fractional). -/
def storeInv (γs : InmemNames) (i : Loc) (q : Qp) : IProp GF :=
  iprop(∃ c : Conc, ghostVar γs.conc q c ∗ storeBody γs i c q)

instance typedPointsto_own_fractional {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    Fractional (fun q : Qp => typedPointsto (GF := GF) l v (DFrac.own q)) where
  fractional q1 q2 := typedPointsto_frac_add l v q1 q2

instance storeBody_fractional (γs : InmemNames) (i : Loc) (c : Conc) :
    Fractional (storeBody (GF := GF) γs i c) := by
  have h1 := ownMap_fractional (GF := GF) c.mlog c.lm
  have h2 := ownMap_fractional (GF := GF) c.mkv c.kvm
  have h3 := ownMap_fractional (GF := GF) c.mint c.st.ints
  have h4 := ghostVar_half_fractional (GF := GF) γs.log c.L
  have h5 := ghostVar_half_fractional (GF := GF) γs.kv c.st
  unfold storeBody
  infer_instance

instance storeInv_fractional (γs : InmemNames) (i : Loc) :
    Fractional (storeInv (GF := GF) γs i) where
  fractional q1 q2 := by
    unfold storeInv
    constructor
    · iintro ⟨%c, Hg, Hb⟩
      icases (ghostVar_fractional (GF := GF) γs.conc c).fractional q1 q2 |>.mp $$ Hg
        with ⟨Hg1, Hg2⟩
      icases (storeBody_fractional γs i c).fractional q1 q2 |>.mp $$ Hb with ⟨Hb1, Hb2⟩
      isplitl [Hg1 Hb1]
      · iexists c; iframe
      · iexists c; iframe
    · iintro ⟨⟨%c1, Hg1, Hb1⟩, ⟨%c2, Hg2, Hb2⟩⟩
      icombine Hg1 Hg2 gives %Hc2
      obtain ⟨_, Hc⟩ := Hc2
      subst Hc
      iexists c1
      isplitl [Hg1 Hg2]
      · iapply ((ghostVar_fractional (GF := GF) γs.conc c1).fractional q1 q2).mpr; iframe
      · iapply ((storeBody_fractional γs i c1).fractional q1 q2).mpr; iframe

/-- The lock invariant, unfolded. -/
theorem storeInv_unfold (γs : InmemNames) (i : Loc) (q : Qp) :
    storeInv (GF := GF) γs i q ⊣⊢ ∃ c : Conc, ghostVar γs.conc q c ∗
      i.[InmemStore, go!"lowIndex"] ↦{DFrac.own q} c.lo ∗
      i.[InmemStore, go!"highIndex"] ↦{DFrac.own q} c.L.hi ∗
      i.[InmemStore, go!"logs"] ↦{DFrac.own q} c.mlog ∗
      c.mlog ↦${DFrac.own q} c.lm ∗
      i.[InmemStore, go!"kv"] ↦{DFrac.own q} c.mkv ∗
      c.mkv ↦${DFrac.own q} c.kvm ∗
      i.[InmemStore, go!"kvInt"] ↦{DFrac.own q} c.mint ∗
      c.mint ↦${DFrac.own q} c.st.ints ∗
      ghostVar γs.log q.half c.L ∗
      ghostVar γs.kv q.half c.st ∗
      ⌜concOk c⌝ ∗ concPers c := by
  unfold storeInv storeBody; exact .rfl

/-- The client's exclusive view of the log contents. -/
def inmemLogs (γs : InmemNames) (A : LogAbs) : IProp GF := ghostVar γs.log (1 : Qp).half A

/-- The client's exclusive view of the stable-store contents. -/
def kvView (γs : InmemNames) (st : StableAbs) : IProp GF := ghostVar γs.kv (1 : Qp).half st

instance inmemLogs_timeless γs L : Timeless (inmemLogs (GF := GF) γs L) := by
  unfold inmemLogs; infer_instance
instance kvView_timeless γs st : Timeless (kvView (GF := GF) γs st) := by
  unfold kvView; infer_instance

/-- `ErrLogNotFound` holds a non-nil error (what `GetLog`'s miss returns). -/
def errLogNotFoundOk : IProp GF :=
  iprop(∃ v : GoInterface, globalAddr ErrLogNotFound ↦□ v ∗ ⌜v ≠ interface.nil⌝)

instance errLogNotFoundOk_persistent : Persistent (errLogNotFoundOk (GF := GF)) := by
  unfold errLogNotFoundOk; infer_instance

/-- The package-initialized fact `errors.newVar` of `ErrLogNotFound` gives `errLogNotFoundOk`. -/
theorem errLogNotFoundOk_of_newVar (msg : GoString) :
    errors.newVar (GF := GF) ErrLogNotFound msg ⊢ errLogNotFoundOk := by
  unfold errors.newVar errLogNotFoundOk
  iintro ⟨%x, #Hx, -⟩
  iexists _
  iframe #
  ipureintro
  simp [interface.mkOk, interface.nil]

/-- The reader-token pool of the store at `i`. -/
def inmemPool (γs : InmemNames) (i : Loc) : IProp GF :=
  iprop(∃ γp : GName, qpool.isQPool inmemPoolN γp
    (sync.ownRWMutex (i.[InmemStore, go!"l"]) (storeInv γs i)))

instance inmemPool_persistent γs i : Persistent (inmemPool (GF := GF) γs i) := by
  unfold inmemPool; infer_instance

/-- **The persistent handle on the `*InmemStore` `i`.** -/
def isInmemStore (γs : InmemNames) (i : Loc) : IProp GF :=
  iprop("#Hinit" ∷ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
    "#Herr" ∷ errLogNotFoundOk ∗
    "#Hguard" ∷ sync.isRWMutexGuard (i.[InmemStore, go!"l"]) (storeInv γs i) ∗
    "#Hpool" ∷ inmemPool γs i)

instance isInmemStore_persistent γs i : Persistent (isInmemStore (GF := GF) γs i) := by
  unfold isInmemStore; infer_instance

/-! ### Ghost helpers -/

theorem inmemLogs_agree (γs : InmemNames) (q : Qp) (L L' : LogAbs) :
    ⊢ inmemLogs (GF := GF) γs L -∗ ghostVar γs.log q L' -∗ ⌜L = L'⌝ := by
  unfold inmemLogs
  iintro H1 H2
  ihave %H := ghostVar_agree _ _ _ _ _ $$ H1 H2
  ipureintro; exact H

theorem kvView_agree (γs : InmemNames) (q : Qp) (st st' : StableAbs) :
    ⊢ kvView (GF := GF) γs st -∗ ghostVar γs.kv q st' -∗ ⌜st = st'⌝ := by
  unfold kvView
  iintro H1 H2
  ihave %H := ghostVar_agree _ _ _ _ _ $$ H1 H2
  ipureintro; exact H

theorem inmemLogs_update (γs : InmemNames) (L L' Lnew : LogAbs) :
    ⊢ inmemLogs (GF := GF) γs L -∗ ghostVar γs.log (1 : Qp).half L' ==∗
      inmemLogs γs Lnew ∗ ghostVar γs.log (1 : Qp).half Lnew := by
  unfold inmemLogs
  iintro H1 H2
  imod ghostVar_update_halves Lnew γs.log L L' $$ H1 H2 with ⟨H1, H2⟩
  imodintro; iframe

theorem kvView_update (γs : InmemNames) (st st' stnew : StableAbs) :
    ⊢ kvView (GF := GF) γs st -∗ ghostVar γs.kv (1 : Qp).half st' ==∗
      kvView γs stnew ∗ ghostVar γs.kv (1 : Qp).half stnew := by
  unfold kvView
  iintro H1 H2
  imod ghostVar_update_halves stnew γs.kv st st' $$ H1 H2 with ⟨H1, H2⟩
  imodintro; iframe

theorem conc_update (γs : InmemNames) (c c' : Conc) :
    ⊢ ghostVar (GF := GF) γs.conc 1 c ==∗ ghostVar γs.conc 1 c' :=
  ghostVar_update c' γs.conc c

end defs

end github_com.hashicorp.raft

end Perennial
