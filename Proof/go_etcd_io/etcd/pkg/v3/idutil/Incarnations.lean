/-
**Request ids across a member's incarnations: the cluster's id state keyed by incarnation**
(the restart plan's R2c, 2026-11-02, `notes/restart-plan.md`, "R2c: what a restart needs of the
cluster's id state"; DRAFT: statements beside `Defs.lean`'s, laws `sorry`, nothing uses them yet).
Lean-first (no Rocq counterpart).

**Why.** `Defs.lean` keys a member's share of the cluster's id state by its 16-bit prefix: its entry
of the issued-ids map (`γi.pfx ↪[γi.cnt] L`, inside its generator's invariant), its cell of the
registries' map (`idWaitIs`, set once, persistently) and the claimers' facts (`Φs pfx`, certificates
in the member's store). A stopped incarnation keeps all three for good (its generator, its wait
registry and its store stay reachable from its in-flight handlers), so a restarted member, under
the same prefix, could get none of them. Here they are keyed by `IdKey`, a prefix and an
incarnation number: each incarnation has its own entry, cell and facts, and a claim records the
incarnation that made it.

* `IdNamesK`: `IdNames` with the key in place of the prefix.
* `idClusterOkK`, `idClusterInvK`: the cluster's claims, as `idClusterOk`/`idClusterInv`, with the
  issued-ids lists per key, an id in one key's list only, and a claim's incarnation its issuer's.
* `idClaimK` (any incarnation's claim, what `entryWaitOk` reads of a committed entry) and
  `idClaimFactK`: the facts per key. `idClaim_factK`: an incarnation reads the claimer's fact of a
  claim of its own key only. Of another key's claim, its own prefix's included, it reads nothing:
  no waiter of it is here (the apply thread's empty floor, as for another member's ids today).
* `idIncLatest`: a member's latest incarnation number, half the member's (handed on in its data
  directory's image), half the cluster invariant's; `idIncarnation_alloc` makes the next
  incarnation's share (its key's empty entry, its wait slots, its registry cell).

**The assumption** (`idNoClash`; the paper's approach for the large-but-finite limits it found in
`idutil` and `sync.RWMutex`, `/shared/grove-paper/sosp26/rwmutex.tex`: assume the limit is never
reached where it is reached, and keep the specs free of it). Two incarnations of one member issue
ids under the same prefix, each generator's suffix starting from the wall clock's milliseconds
shifted by 8 (`NewGenerator(uint16(memberID), time.Now())`), and the old incarnation's in-flight
handlers can still call `Next` after `HardStop`. Their ids are distinct only if the clock does not
step back and the member issues fewer than 256 ids per millisecond on average
(`issues/etcd-request-id-restart-reuse.md`). `idNoClash` states it where it is used, at `Next`: the
id a generator issues is in no other key's list. It is false of some executions (a clock stepped
back; two generators made with one prefix and one time), which is why it is a named statement, to be
an axiom at the trust boundary once reviewed (the `axiom` skill), and recorded with the issue. Across
members, nothing changes: prefixes differ (`idPfxOk`, distinct), proved as today.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- **A member incarnation's key**: its prefix (`idPfxOf memberID`) and its incarnation number (`0`
for a member's first start, one more at each restart). -/
abbrev IdKey := w64 × Nat

/-- **An incarnation's id names** (`IdNames` with `key` in place of `pfx`): the cluster's issued-ids
map (an id's claim records its incarnation) and keys' map (the ids each key issued), the
incarnation's own wait slots, its key, the cluster's registries' map (keyed by key), and (new) the
cluster's latest-incarnation map (keyed by prefix). -/
structure IdNamesK where
  issued : GName
  cnt : GName
  slot : GName
  key : IdKey
  wn : GName
  incs : GName

/-- The incarnation's prefix. -/
abbrev IdNamesK.pfx (γi : IdNamesK) : w64 := γi.key.1

/-- The incarnation's number. -/
abbrev IdNamesK.inc (γi : IdNamesK) : Nat := γi.key.2

/-- **The cluster's ids, by key** (`idClusterOk`'s, keyed): the issued-ids map `I` holds the
reserved `0` and exactly the ids the keys' lists `C` hold; each key's prefix good and its ids of
it; an id in one key's list only (across members by prefix; across one member's incarnations, the
assumption `idNoClash`); a claim's incarnation that of the key that issued it; and every key's
incarnation at most its prefix's latest in `N`. -/
def idClusterOkK (I : GMap w64 (Option (List w8 × GName × Nat))) (C : GMap IdKey (List w64))
    (N : GMap w64 Nat) : Prop :=
  (∀ id, (I !! id).isSome ↔ id = W64 0 ∨ ∃ k L, C !! k = some L ∧ id ∈ L) ∧
  (∀ k L, C !! k = some L → idPfxOk k.1 ∧ ∀ id ∈ L, idPfx id = k.1) ∧
  (∀ k k' L L' id, C !! k = some L → C !! k' = some L' → id ∈ L → id ∈ L' → k = k') ∧
  (∀ id d γf inc, I !! id = some (some (d, γf, inc)) →
    ∃ L, C !! (idPfx id, inc) = some L ∧ id ∈ L) ∧
  (∀ k L, C !! k = some L → ∃ n, N !! k.1 = some n ∧ k.2 ≤ n)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The right to claim `id` (`idUnclaimed`'s). -/
def idUnclaimedK (γi : IdNamesK) (id : w64) : IProp GF :=
  id ↪[γi.issued] (none : Option (List w8 × GName × Nat))

/-- **The id `id` was claimed for `d`, with the claimer's name `γf`, by some incarnation**
(persistent): what a committed entry's reader knows (`entryWaitOk`), whoever proposed it. -/
def idClaimK (γi : IdNamesK) (id : w64) (d : List w8) (γf : GName) : IProp GF :=
  iprop(∃ inc : Nat, id ↪[γi.issued]□ some (d, γf, inc))

/-- **The id `id` was claimed by this incarnation** (persistent): what the proposer makes. -/
def idClaimOwnK (γi : IdNamesK) (id : w64) (d : List w8) (γf : GName) : IProp GF :=
  id ↪[γi.issued]□ some (d, γf, γi.inc)

instance idClaimK_persistent (γi : IdNamesK) (id : w64) (d : List w8) (γf : GName) :
    Persistent (idClaimK (GF := GF) γi id d γf) := by
  unfold idClaimK; infer_instance

instance idClaimOwnK_persistent (γi : IdNamesK) (id : w64) (d : List w8) (γf : GName) :
    Persistent (idClaimOwnK (GF := GF) γi id d γf) := by
  unfold idClaimOwnK; infer_instance

/-- The claimer's fact of the entry `v` of the id `id`, by its key's `Φs`. -/
def idClaimFactK (Φs : IdKey → w64 → List w8 → GName → IProp GF) (id : w64)
    (v : Option (List w8 × GName × Nat)) : IProp GF :=
  match v with
  | some (d, γf, inc) => iprop(□ Φs (idPfx id, inc) id d γf)
  | none => iprop(True)

instance idClaimFactK_persistent (Φs : IdKey → w64 → List w8 → GName → IProp GF) (id : w64)
    (v : Option (List w8 × GName × Nat)) : Persistent (idClaimFactK Φs id v) := by
  rcases v with _ | ⟨d, γf, inc⟩ <;> unfold idClaimFactK <;> infer_instance

/-- **The cluster's claims, by key** (persistent; `idClusterInv`'s): the issued-ids map, the keys'
map, the latest-incarnation map (half: each prefix's other half is its member's, `idIncLatest`),
`idClusterOkK`, the claimers' facts; and (new) the registries' map's authority, so that a restart
can add its key's cell (today `idWait_alloc_list` makes every prefix's cell once). -/
def idClusterInvK (issued cnt incs wn : GName) (Φs : IdKey → w64 → List w8 → GName → IProp GF) :
    IProp GF :=
  inv idClusterN iprop(∃ (I : GMap w64 (Option (List w8 × GName × Nat)))
      (C : GMap IdKey (List w64)) (N : GMap w64 Nat) (R : GMap IdKey GName),
    ghostMapAuth issued 1 I ∗ ghostMapAuth cnt 1 C ∗ ghostMapAuth incs (1 : Qp).half N ∗
    ghostMapAuth wn 1 R ∗
    ⌜idClusterOkK I C N ∧ ∀ k, (R !! k).isSome → ∃ n, N !! k.1 = some n ∧ k.2 ≤ n⌝ ∗
    [∗map] id ↦ v ∈ I, idClaimFactK Φs id v)

instance idClusterInvK_persistent (issued cnt incs wn : GName)
    (Φs : IdKey → w64 → List w8 → GName → IProp GF) :
    Persistent (idClusterInvK (GF := GF) issued cnt incs wn Φs) := by
  unfold idClusterInvK; infer_instance

/-- **The member of prefix `p`'s latest incarnation is `n`** (exclusive; the member's half of the
latest-incarnation map's entry): its first start has `0`; each restart takes it from the stopped
incarnation's data-directory image and makes the next (`idIncarnation_alloc`). -/
def idIncLatest (incs : GName) (p : w64) (n : Nat) : IProp GF :=
  p ↪[incs]{DFrac.own (1 : Qp).half} n

/-- **An incarnation's share of the cluster's ids** (`idShare`'s): its key's entry of the keys' map,
empty, and its wait slots' map, empty. -/
def idShareK (γi : IdNamesK) : IProp GF :=
  iprop(γi.key ↪[γi.cnt] ([] : List w64) ∗ ghostMapAuth γi.slot 1 (∅ : GMap w64 Unit))

/-- **An incarnation's cell of the registries' map, not yet set** (`idWaitTokAt`'s, by key; `slot` unread). -/
def idWaitTokK (γi : IdNamesK) : IProp GF :=
  iprop(∃ γp : GName, γi.key ↪[γi.wn]□ γp ∗ dghostVar γp (DFrac.own 1) (none : Option GName))

/-- **The incarnation of key `k` registers its requests in `W`** (persistent; `idWaitIs`'s). -/
def idWaitIsK (γi : IdNamesK) (k : IdKey) (W : GName) : IProp GF :=
  iprop(∃ γp : GName, k ↪[γi.wn]□ γp ∗ dghostVar γp DFrac.discard (some W))

/-- **An id nobody holds** (`idFresh`'s): its claim, its wait slot, and its prefix the
incarnation's. -/
def idFreshK (γi : IdNamesK) (id : w64) : IProp GF :=
  iprop(idUnclaimedK γi id ∗ id ↪[γi.slot] () ∗ ⌜idPfx id = γi.pfx⌝)

/-- **The generator `g` of an incarnation** (persistent; `idGen`'s, with its key's entry): its
prefix, its suffix with the issued count `k` and `k` receipts, its key's list `L` and its wait
slots (the ids issued, and only those, in both), and the cluster's claims, whose facts at its key
are `Φ`. -/
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
    ∃ Φs : IdKey → w64 → List w8 → GName → IProp GF, ⌜Φs γi.key = Φ⌝ ∗
      idClusterInvK γi.issued γi.cnt γi.incs γi.wn Φs)

instance idGenK_persistent (γi : IdNamesK) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) :
    Persistent (idGenK (GF := GF) γi g Φ) := by
  unfold idGenK; infer_instance

/-- **The assumption: an incarnation's generator issues no id another key issued** (DRAFT; see
the file header). At `Next`'s increment of the generator `g` of the key `γi.key`, the id it makes
from the new suffix is in no other key's list of the cluster's keys' map. (Only the same prefix's
other incarnations can hold it: other prefixes' ids differ in their 16 high bits.) Stated over the
generator's suffix cell and the keys' map's authority, so that it speaks of a real generator's step;
the `axiom` skill's review decides its final form. -/
def idNoClash : Prop :=
  ∀ (γi : IdNamesK) (g : Loc) (s : w64) (C : GMap IdKey (List w64)),
    structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"suffix" g ↦ s ∗
      structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"prefix" g ↦□ γi.pfx ∗
      ghostMapAuth γi.cnt 1 C ⊢
    ⌜∀ k L, k ≠ γi.key → C !! k = some L →
      (γi.pfx ||| ((s + W64 1) &&& W64 (2 ^ 48 - 1))) ∉ L⌝

/-! ### The laws a restart needs (the allocations DRAFT, as statements; the claim laws proved) -/

/-- **The cluster's claims, allocated, by key** (`idCluster_alloc`'s): for the members' prefixes
`ps` (good, distinct), each member's first incarnation's entry (key `(p, 0)`, empty) and its latest
incarnation `0`. -/
def idClusterK_alloc : Prop :=
  ∀ (ps : List w64) (Φs : IdKey → w64 → List w8 → GName → IProp GF) (E : CoPset),
    ps.Nodup → (∀ p ∈ ps, idPfxOk p) →
    ⊢ |={E}=> ∃ issued cnt incs wn : GName, idClusterInvK (GF := GF) issued cnt incs wn Φs ∗
      (W64 0) ↪[issued]□ (none : Option (List w8 × GName × Nat)) ∗
      [∗list] p ∈ ps, (p, 0) ↪[cnt] ([] : List w64) ∗ idIncLatest incs p 0 ∗
        ∃ slot : GName, idWaitTokK ⟨issued, cnt, slot, (p, 0), wn, incs⟩

/-- **The next incarnation's share** (a restart's allocation): from the member's latest incarnation
`n`, its latest becomes `n + 1`, with key `(p, n + 1)`'s empty entry, a new wait slots' map and its
cell of the registries' map. -/
def idIncarnation_alloc : Prop :=
  ∀ (issued cnt incs wn : GName) (Φs : IdKey → w64 → List w8 → GName → IProp GF) (p : w64)
    (n : Nat) (E : CoPset), ↑idClusterN ⊆ E → idPfxOk p →
    ⊢ idClusterInvK (GF := GF) issued cnt incs wn Φs -∗ idIncLatest incs p n ={E}=∗
      ∃ slot : GName,
        idIncLatest incs p (n + 1) ∗ idShareK ⟨issued, cnt, slot, (p, n + 1), wn, incs⟩ ∗
        idWaitTokK ⟨issued, cnt, slot, (p, n + 1), wn, incs⟩

/-- **The claimer's fact, of a claim of the incarnation's own key** (`idClaim_fact`'s): the
generator's `Φ`. A claim of another key (another member's, or another incarnation of this one) gives
nothing here. -/
theorem idClaim_factK (γi : IdNamesK) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) (id : w64)
    (d : List w8) (γf : GName) (E : CoPset) (HE : ↑idClusterN ⊆ E) :
    ⊢ idGenK (GF := GF) γi g Φ -∗ idClaimOwnK γi id d γf -∗ ⌜idPfx id = γi.pfx⌝ ={E}=∗
      ▷ □ Φ id d γf := by
  iintro #Hg #Hc %Hp
  iunfold idGenK at Hg
  icases Hg with ⟨%s0, %Hgn, #Hpfx, %Hs0, #Hinv, %Φs, %HΦs, #Hcl⟩
  iunfold idClusterInvK at Hcl
  iinv Hcl with Hi Hclose
  icases Hi with ⟨%I, %C, %N, %R, >HI, >HC, >HN, >HR, >%Hok, #HF⟩
  iunfold idClaimOwnK at Hc
  ihave %Hlk := ghost_map_lookup $$ HI Hc
  have hΦ : Φs (idPfx id, γi.inc) = Φ := by rw [Hp, ← HΦs]
  ihave #Hf : iprop(▷ □ Φ id d γf) $$ []
  · inext
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := I)
      (Φ := fun id v => idClaimFactK Φs id v) Hlk).1 $$ HF with ⟨Hf, -⟩
    iunfold idClaimFactK at Hf
    simp only [hΦ]
    iexact Hf
  imod Hclose $$ [HI HC HN HR] with -
  · inext
    iexists I, C, N, R
    iframe HI HC HN HR HF
    ipureintro; exact Hok
  imodintro
  iexact Hf

/-- **A claim is its own key's or not** (decided by the claim's incarnation): what the apply thread
cases on in place of the id's prefix. -/
theorem idClaimK_own_or (γi : IdNamesK) (id : w64) (d : List w8) (γf : GName) :
    ⊢ idClaimK (GF := GF) γi id d γf -∗
      idClaimOwnK γi id d γf ∨ ∃ inc : Nat, ⌜inc ≠ γi.inc⌝ ∗ id ↪[γi.issued]□ some (d, γf, inc) := by
  iintro #Hc
  iunfold idClaimK at Hc
  icases Hc with ⟨%inc, #Hc⟩
  by_cases h : inc = γi.inc
  · subst h
    ileft
    iunfold idClaimOwnK
    iexact Hc
  · iright
    iexists inc
    iframe Hc
    ipureintro; exact h

end defs

/-! ### The generator's specs at a key (DRAFT) -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.idutil.Assumptions]

/-- **`NewGenerator` at an incarnation's key** (`NewGenerator.spec`'s, with the key's share): no
premise on `now`; the assumption is at `Next`. -/
def NewGenerator_specK : Prop :=
  ∀ (γi : IdNamesK) (memberID : w16) (now : time.Time)
    (Φs : IdKey → w64 → List w8 → GName → IProp GF),
  γi.pfx = idPfxOf memberID →
  ⊢ {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil ∗ idShareK γi ∗
        idClusterInvK γi.issued γi.cnt γi.incs γi.wn Φs }}
      (App (App (Val (@! go_etcd_io.etcd.pkg.v3.idutil.NewGenerator)) (Val #memberID)) (Val #now))
    {{ (g : Loc), RET #g; idGenK γi g (Φs γi.key) }}

/-- **`Next` at an incarnation's key** (`Generator.Next.spec`'s): an id nobody holds; proved from
`idNoClash` (an id another incarnation of the prefix issued would be held). -/
def Next_specK : Prop :=
  ∀ (γi : IdNamesK) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF),
  ⊢ {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil ∗ idGenK γi g Φ }}
      (App (Val (g @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.idutil.Generator.ty @!! go!"Next"))
        (Val #()))
    {{ (id : w64), RET #id; idFreshK γi id }}

end specs

end EtcdGrove
end Perennial
