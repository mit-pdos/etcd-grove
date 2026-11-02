/-
**Request ids across a member's incarnations: the cluster's id state keyed by incarnation**
(the restart plan's R2c, 2026-11-02, `notes/restart-plan.md`, "R2c: what a restart needs of the
cluster's id state"; DRAFT: statements beside `Defs.lean`'s, nothing uses them yet; revised after
the first review, `notes/restart-plan.md`, "R2c review, round 1"). Lean-first (no Rocq counterpart).

**Why.** `Defs.lean` keys a member's share of the cluster's id state by its 16-bit prefix: its entry
of the issued-ids map (inside its generator's invariant), its cell of the registries' map (set once,
persistently) and the claimers' facts (`Φs pfx`, fixed when the cluster is allocated: certificates in
the member's first store). A stopped incarnation keeps all three for good (its generator, its wait
registry and its store stay reachable from its in-flight handlers), so a restarted member, under the
same prefix, could get none of them. Here they are keyed by `IdKey`, a prefix and an incarnation
number, and each key's facts are given when the key is made, as a saved predicate, not fixed with
the cluster (a restarted incarnation's store does not exist when the cluster is allocated).

* `idClusterInvK`: the issued-ids map (a claim records the key of its claimer), the keys' lists, the
  registries' cells and the keys' facts, one domain for the last three; an id in one key's list only.
* `idIncarnation_alloc`: a new key of a good prefix, at an incarnation number no key of the prefix
  has (chosen from the finite maps: nothing is handed from one incarnation to the next), with its
  facts `Φ` (`idKeyFact`), its empty list and wait slots (`idShareK`) and its unset registry cell
  (`idWaitTokK`). A member's first start and each restart both use it.
* `idClaimK` (a claim by some key, what a committed entry's reader knows) and `idClaimOwnK` (by the
  incarnation's own key); `idClaimK_own_or`: one or the other. `idClaim_factK`: of its own key's
  claim, an incarnation reads the claimer's fact. Of another key's claim (another member's, or an
  earlier incarnation of its own) it reads nothing, and needs nothing: a waiter of the incarnation
  holds an own-key claim of its id, and two claims of one id agree (`idClaimK_agree`), so no waiter
  of it is here (the apply thread's empty floor, as for another member's ids today).

**The assumption: ids of a member's incarnations do not clash** (the paper's approach for
`idutil`'s large-but-finite limit, `/shared/grove-paper/sosp26/case.tex` and `rwmutex.tex`: assume the
limit is never reached where it is reached, in the program's semantics, and keep the specs free of
it). Two incarnations of one member issue ids under one prefix, each generator's suffix starting from
the wall clock (`NewGenerator(uint16(memberID), time.Now())`); the old incarnation's in-flight
handlers can still call `Next` after `HardStop`. Their ids are distinct only if the clock does not
step back and the member issues fewer than 256 ids per millisecond on average
(`issues/etcd-request-id-restart-reuse.md`). A statement of it in the logic (the first draft's
`idNoClash`, over the keys' map's authority) is refutable (a fabricated map; or two generators made
at one time, which the model's `time.Now` allows) and would make Lean inconsistent. So it goes into
the semantics: `Generator.Next` becomes a trusted model (`TrustedCode`, the Goose configuration's
`trusted`), the Go body followed by `primitive.Assume(issuedBy[id] == nil || issuedBy[id] == g)` and
`issuedBy[id] = g`, over a model-only package variable `issuedBy` (id to generator) the cluster
invariant owns. A false `Assume` does not return (Perennial's `Assume.spec`), so the model excludes
exactly the executions where two generators issue one id, and no statement is left to refute. Its
faithfulness is the issue's precondition, recorded there. `Next_specK` is proved from it. Across
members nothing changes: prefixes differ (`idPfxOk`, distinct), proved as today.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Defs
public import Perennial.Ghost.SavedProp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- **A member incarnation's key**: its prefix (`idPfxOf memberID`) and its incarnation number. -/
abbrev IdKey := w64 × Nat

/-- **A claim** (an entry of the issued-ids map, once claimed): the request's data, the claimer's
ghost name, the claimer's key. -/
abbrev IdClaimV := List w8 × GName × IdKey

/-- **An incarnation's id names** (`IdNames` with `key` in place of `pfx`): the cluster's issued-ids
map, keys' lists, registries' cells and keys' facts; the incarnation's own wait slots and key. -/
structure IdNamesK where
  issued : GName
  cnt : GName
  wn : GName
  fs : GName
  slot : GName
  key : IdKey

/-- The incarnation's prefix. -/
abbrev IdNamesK.pfx (γi : IdNamesK) : w64 := γi.key.1

/-- **The cluster's ids, by key** (`idClusterOk`'s, keyed): the issued-ids map `I` holds the
reserved `0` and exactly the ids of the keys' lists `C`; each key's prefix good and its ids of it;
an id in one key's list only (across members by prefix; across one member's incarnations by the
trusted `Next`'s assumption); the keys' lists, registries' cells `R` and facts `Fm` of one domain. -/
def idClusterOkK (I : GMap w64 (Option IdClaimV)) (C : GMap IdKey (List w64))
    (R : GMap IdKey GName) (Fm : GMap IdKey GName) : Prop :=
  (∀ id, (I !! id).isSome ↔ id = W64 0 ∨ ∃ k L, C !! k = some L ∧ id ∈ L) ∧
  (∀ k L, C !! k = some L → idPfxOk k.1 ∧ ∀ id ∈ L, idPfx id = k.1) ∧
  (∀ k k' L L' id, C !! k = some L → C !! k' = some L' → id ∈ L → id ∈ L' → k = k') ∧
  (∀ k, (C !! k).isSome ↔ (R !! k).isSome) ∧ (∀ k, (C !! k).isSome ↔ (Fm !! k).isSome)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The facts of key `k`'s claims are `Φ`** (persistent): the key's element of the keys' facts
map names a saved predicate of `Φ`. -/
def idKeyFactAt (fs : GName) (k : IdKey) (Φ : w64 → List w8 → GName → IProp GF) : IProp GF :=
  iprop(∃ γΦ : GName, k ↪[fs]□ γΦ ∗
    savedPredOwn γΦ DFrac.discard (fun x : w64 × List w8 × GName => Φ x.1 x.2.1 x.2.2))

instance idKeyFactAt_persistent (fs : GName) (k : IdKey) (Φ : w64 → List w8 → GName → IProp GF) :
    Persistent (idKeyFactAt (GF := GF) fs k Φ) := by
  unfold idKeyFactAt; infer_instance

/-- `idKeyFactAt` at the incarnation's own key. -/
abbrev idKeyFact (γi : IdNamesK) (Φ : w64 → List w8 → GName → IProp GF) : IProp GF :=
  idKeyFactAt γi.fs γi.key Φ

/-- The claimer's fact of the entry `v` of `id`: its key's facts, whatever they are. -/
def idClaimFactK (fs : GName) (id : w64) (v : Option IdClaimV) : IProp GF :=
  match v with
  | some (d, γf, k) => iprop(∃ Φ : w64 → List w8 → GName → IProp GF,
      idKeyFactAt fs k Φ ∗ □ Φ id d γf)
  | none => iprop(True)

instance idClaimFactK_persistent (fs : GName) (id : w64) (v : Option IdClaimV) :
    Persistent (idClaimFactK (GF := GF) fs id v) := by
  rcases v with _ | ⟨d, γf, k⟩ <;> unfold idClaimFactK <;> infer_instance

/-- **The cluster's claims, by key** (persistent; `idClusterInv`'s): the four maps' authorities,
`idClusterOkK`, the claimers' facts. -/
def idClusterInvK (issued cnt wn fs : GName) : IProp GF :=
  inv idClusterN iprop(∃ (I : GMap w64 (Option IdClaimV)) (C : GMap IdKey (List w64))
      (R : GMap IdKey GName) (Fm : GMap IdKey GName),
    ghostMapAuth issued 1 I ∗ ghostMapAuth cnt 1 C ∗ ghostMapAuth wn 1 R ∗ ghostMapAuth fs 1 Fm ∗
    ⌜idClusterOkK I C R Fm⌝ ∗ [∗map] id ↦ v ∈ I, idClaimFactK fs id v)

instance idClusterInvK_persistent (issued cnt wn fs : GName) :
    Persistent (idClusterInvK (GF := GF) issued cnt wn fs) := by
  unfold idClusterInvK; infer_instance

/-- `idClusterInvK` at the incarnation's names. -/
abbrev idClusterK (γi : IdNamesK) : IProp GF := idClusterInvK γi.issued γi.cnt γi.wn γi.fs

/-- **No request claims the id `0`** (persistent; `idNoZero`'s). -/
def idNoZeroK (γi : IdNamesK) : IProp GF := (W64 0) ↪[γi.issued]□ (none : Option IdClaimV)

/-- The right to claim `id` (`idUnclaimed`'s). -/
def idUnclaimedK (γi : IdNamesK) (id : w64) : IProp GF :=
  id ↪[γi.issued] (none : Option IdClaimV)

/-- **`id` was claimed for `d`, with the claimer's name `γf`, by some key** (persistent): what a
committed entry's reader knows (`entryWaitOk`), whoever proposed it. -/
def idClaimK (γi : IdNamesK) (id : w64) (d : List w8) (γf : GName) : IProp GF :=
  iprop(∃ k : IdKey, id ↪[γi.issued]□ some (d, γf, k))

/-- **`id` was claimed by this incarnation** (persistent; what its proposer makes). -/
def idClaimOwnK (γi : IdNamesK) (id : w64) (d : List w8) (γf : GName) : IProp GF :=
  id ↪[γi.issued]□ some (d, γf, γi.key)

instance idClaimK_persistent (γi : IdNamesK) (id : w64) (d : List w8) (γf : GName) :
    Persistent (idClaimK (GF := GF) γi id d γf) := by
  unfold idClaimK; infer_instance

instance idClaimOwnK_persistent (γi : IdNamesK) (id : w64) (d : List w8) (γf : GName) :
    Persistent (idClaimOwnK (GF := GF) γi id d γf) := by
  unfold idClaimOwnK; infer_instance

/-- **An incarnation's share** (`idShare`'s): its key's list, empty, and its wait slots' map. -/
def idShareK (γi : IdNamesK) : IProp GF :=
  iprop(γi.key ↪[γi.cnt] ([] : List w64) ∗ ghostMapAuth γi.slot 1 (∅ : GMap w64 Unit))

/-- **Key `k`'s registry cell, not yet set** (`idWaitTokAt`'s, by key). -/
def idWaitTokK (wn : GName) (k : IdKey) : IProp GF :=
  iprop(∃ γp : GName, k ↪[wn]□ γp ∗ dghostVar γp (DFrac.own 1) (none : Option GName))

/-- **Key `k`'s incarnation registers its requests in `W`** (persistent; `idWaitIs`'s). -/
def idWaitIsK (wn : GName) (k : IdKey) (W : GName) : IProp GF :=
  iprop(∃ γp : GName, k ↪[wn]□ γp ∗ dghostVar γp DFrac.discard (some W))

instance idWaitIsK_persistent (wn : GName) (k : IdKey) (W : GName) :
    Persistent (idWaitIsK (GF := GF) wn k W) := by
  unfold idWaitIsK; infer_instance

/-- **An id nobody holds** (`idFresh`'s). -/
def idFreshK (γi : IdNamesK) (id : w64) : IProp GF :=
  iprop(idUnclaimedK γi id ∗ id ↪[γi.slot] () ∗ ⌜idPfx id = γi.pfx⌝)

/-- **The generator `g` of an incarnation** (persistent; `idGen`'s): its key's list in its
invariant, and its key's facts `Φ`. (The trusted `Next`'s model-only `issuedBy` map, with its
`Assume`, is the refactor's.) -/
def idGenK (γi : IdNamesK) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) : IProp GF :=
  iprop(∃ s0 : w64, ⌜g ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"prefix" g ↦□ γi.pfx ∗
    ⌜uint.Z s0 < 2 ^ 48 ∧ γi.pfx &&& W64 (2 ^ 48 - 1) = W64 0⌝ ∗
    inv idN iprop(∃ (k : Nat) (L : List w64) (S : GMap w64 Unit),
      structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"suffix" g ↦
        (s0 + W64 (k : Int)) ∗
      ⧗ k ∗
      γi.key ↪[γi.cnt] L ∗ ghostMapAuth γi.slot 1 S ∗
      ⌜∀ id, (id ∈ L ↔ idIssued γi.pfx s0 k id) ∧ ((S !! id).isSome ↔ idIssued γi.pfx s0 k id)⌝) ∗
    idKeyFact γi Φ ∗ idClusterK γi)

instance idGenK_persistent (γi : IdNamesK) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) :
    Persistent (idGenK (GF := GF) γi g Φ) := by
  unfold idGenK; infer_instance

/-! ### Laws (proved) -/

/-- **A claim is the incarnation's own key's or another's.** -/
theorem idClaimK_own_or (γi : IdNamesK) (id : w64) (d : List w8) (γf : GName) :
    ⊢ idClaimK (GF := GF) γi id d γf -∗
      idClaimOwnK γi id d γf ∨ ∃ k : IdKey, ⌜k ≠ γi.key⌝ ∗ id ↪[γi.issued]□ some (d, γf, k) := by
  iintro #Hc
  iunfold idClaimK at Hc
  icases Hc with ⟨%k, #Hc⟩
  by_cases h : k = γi.key
  · subst h
    ileft
    iunfold idClaimOwnK
    iexact Hc
  · iright
    iexists k
    iframe Hc
    ipureintro; exact h

/-- **Two claims of one id agree**, keys included: an own-key claim (a waiter's) excludes a claim by
another key (an earlier incarnation's replayed entry). -/
theorem idClaimK_agree (γi : IdNamesK) (id : w64) (v v' : IdClaimV) :
    ⊢ id ↪[γi.issued]□ (some v : Option IdClaimV) -∗ id ↪[γi.issued]□ (some v' : Option IdClaimV) -∗
      ⌜v = v'⌝ := by
  iintro #H1 #H2
  ihave %H := ghostMapElem_agree $$ H1 H2
  ipureintro; exact Option.some.inj H

/-- A key's registry cell is unique. -/
theorem idWaitIsK_agree (wn : GName) (k : IdKey) (W W' : GName) :
    ⊢ idWaitIsK (GF := GF) wn k W -∗ idWaitIsK wn k W' -∗ ⌜W = W'⌝ := by
  unfold idWaitIsK
  iintro ⟨%γp, #H1, #C1⟩ ⟨%γp', #H2, #C2⟩
  ihave %Hp := ghostMapElem_agree $$ H1 H2
  subst Hp
  ihave %Hw := dghostVar_agree γp (some W) DFrac.discard (some W') DFrac.discard $$ C1 C2
  ipureintro
  exact Option.some.inj Hw

/-- Setting a key's registry cell (`idWaitTok_set`'s). -/
theorem idWaitTokK_set (wn : GName) (k : IdKey) (W : GName) :
    ⊢ idWaitTokK (GF := GF) wn k ==∗ idWaitIsK wn k W := by
  unfold idWaitTokK idWaitIsK
  iintro ⟨%γp, #Hp, Hc⟩
  imod dghostVar_update (some W) γp (none : Option GName) $$ Hc with Hc
  imod dghostVar_persist γp 1 (some W) $$ Hc with #Hc
  imodintro
  iexists γp
  iframe Hp Hc

end defs

/-! ### The laws to prove in the refactor, and the generator's specs at a key (DRAFT statements) -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.idutil.Assumptions]

/-- **The cluster's claims, allocated** (`idCluster_alloc`'s): no key yet; the reserved `0`. -/
def idClusterK_alloc : Prop :=
  ∀ (E : CoPset), ⊢ |={E}=> ∃ issued cnt wn fs : GName,
    idClusterInvK (GF := GF) issued cnt wn fs ∗ (W64 0) ↪[issued]□ (none : Option IdClaimV)

/-- **A new incarnation's key** (a member's first start and each restart): of the good prefix `p`,
at an incarnation number no key of `p` has, with its facts `Φ`, its share and its registry cell. -/
def idIncarnation_alloc : Prop :=
  ∀ (issued cnt wn fs : GName) (p : w64) (Φ : w64 → List w8 → GName → IProp GF) (E : CoPset),
    ↑idClusterN ⊆ E → idPfxOk p →
    ⊢ idClusterInvK (GF := GF) issued cnt wn fs ={E}=∗ ∃ (inc : Nat) (slot : GName),
      idKeyFactAt fs (p, inc) Φ ∗ idShareK ⟨issued, cnt, wn, fs, slot, (p, inc)⟩ ∗
      idWaitTokK wn (p, inc)

/-- **The claimer's fact, of a claim of the incarnation's own key** (`idClaim_fact`'s, through the
saved predicate: under a later). -/
def idClaim_factK : Prop :=
  ∀ (γi : IdNamesK) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) (id : w64) (d : List w8)
    (γf : GName) (E : CoPset), ↑idClusterN ⊆ E →
    ⊢ idGenK (GF := GF) γi g Φ -∗ idClaimOwnK γi id d γf ={E}=∗ ▷ □ Φ id d γf

/-- **`NewGenerator` at an incarnation's key** (`NewGenerator.spec`'s): no premise on `now`. -/
def NewGenerator_specK : Prop :=
  ∀ (γi : IdNamesK) (memberID : w16) (now : time.Time) (Φ : w64 → List w8 → GName → IProp GF),
  γi.pfx = idPfxOf memberID →
  ⊢ {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil ∗ idShareK γi ∗
        idKeyFact γi Φ ∗ idClusterK γi }}
      (App (App (Val (@! go_etcd_io.etcd.pkg.v3.idutil.NewGenerator)) (Val #memberID)) (Val #now))
    {{ (g : Loc), RET #g; idGenK γi g Φ }}

/-- **`Next` at an incarnation's key** (`Generator.Next.spec`'s, the receipts' bound `idCred`
kept): an id nobody holds; proved over the trusted `Next`'s `Assume` (see the file header). -/
def Next_specK : Prop :=
  ∀ (γi : IdNamesK) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF),
  ⊢ {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil ∗ idGenK γi g Φ ∗
        idCred (⟨γi.issued, γi.cnt, γi.slot, γi.pfx, γi.wn⟩ : IdNames) 1 }}
      (App (Val (g @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.idutil.Generator.ty @!! go!"Next"))
        (Val #()))
    {{ (id : w64), RET #id; idFreshK γi id }}

end specs

end EtcdGrove
end Perennial
