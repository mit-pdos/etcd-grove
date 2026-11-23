/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Hash.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The hashes of the SwiftPaxos slot (`swift/dpath.go`, under the harness's ideal hash
Perennial's SHA-256 extension: `sha256IsHash` at the global ghost state, `sha256IsHash_inj` under
`netSha_noCollision`, `sha256IsHash_len`): the chained hashes over command
ids, the start-marked path hashes (F2's fix), the dependency hash, `clientChecksum`, and their laws
(moved here from Proof/swift/ChainHash.lean, ChecksumPath.lean, ChecksumStart.lean, change log
C9, so that `Inv.lean`'s `checksum_path`/`checksum_deps` are proved in place):

* `chainHash_suffix`: two chains from the same 32-byte start that end in the same hash are over
  paths one of which is a suffix of the other.
* `startHash_inj`: equal start-marked hashes are of equal paths.
* `startHash_chain_last`: a start-marked hash equal to a chain from a 32-byte start: the paths
  have the same last id (what tells a path hash from the dependency hash).
* `checksum_path_eq`, `checksum_deps_perm`: the laws `checksum_path`, `checksum_deps`.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Defs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

/-- The zero hash (`[32]byte{}`), where `clientChecksum`'s and the frozen path chains start. -/
abbrev zeroHash : Hash := List.replicate 32 (W8 0)

theorem encCmdId_length (x : CmdId) : (encCmdId x).length = 8 := by
  simp [encCmdId, le32, u32Le_length]

theorem encCmdId_inj {x y : CmdId} (h : encCmdId x = encCmdId y) : x = y := by
  unfold encCmdId le32 at h
  have h1 := List.append_inj h (by simp [u32Le_length])
  obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
  simp only at h1
  rw [u32Le_inj h1.1, u32Le_inj h1.2]

theorem eq_nil_or_snoc {α : Type} (l : List α) : l = [] ∨ ∃ L b, l = L ++ [b] := by
  rcases List.eq_nil_or_concat l with h | ⟨L, b, h⟩
  · exact .inl h
  · exact .inr ⟨L, b, by simp [h]⟩

/-- Induction from the end of a list. -/
theorem snoc_induction {α : Type} {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ l a, motive l → motive (l ++ [a])) (l : List α) : motive l := by
  suffices ∀ n (l : List α), l.length = n → motive l from this _ l rfl
  intro n; induction n with
  | zero => intro l hl; rw [List.eq_nil_of_length_eq_zero hl]; exact nil
  | succ n ih =>
    intro l hl
    rcases eq_nil_or_snoc l with rfl | ⟨L, b, rfl⟩
    · exact nil
    · exact snoc L b (ih L (by simp at hl; omega))

/-- A suffix relation survives appending the same last element. -/
theorem suffix_snoc_or {α : Type} {P Q : List α} (x : α) (h : P <:+ Q ∨ Q <:+ P) :
    P ++ [x] <:+ Q ++ [x] ∨ Q ++ [x] <:+ P ++ [x] := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · left; exact ⟨t, by simp⟩
  · right; exact ⟨t, by simp⟩

/-- A non-empty suffix has the list's last element. -/
theorem suffix_getLast? {α : Type} {P Q : List α} (h : P <:+ Q) (hP : P ≠ []) :
    P.getLast? = Q.getLast? := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getLast?_append]
  cases hp : P.getLast? with
  | none => simp_all
  | some a => simp

section ghost
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]

/-! ## Hashes (`swift/dpath.go`, the ideal hash `is_hash`) -/

/-- `h` (32 bytes) is SHA-256 of `data`. -/
def hashOf (data : List w8) (h : Hash) : IProp netDistGF :=
  iprop(∃ a : GoArray w8 32, ⌜a.arr = h⌝ ∗
    sha256IsHash sha256NoCollisionFilter (gooseSha256GS (ok := sha256NoCollisionFilter)) data a)

/-- `hash(initial, cmdId)` chained over `ids` from `init` gives `h`. -/
def chainHash : Hash → List CmdId → Hash → IProp netDistGF
  | init, [], h => iprop(⌜h = init⌝)
  | init, x :: xs, h => iprop(∃ h1, hashOf (init ++ encCmdId x) h1 ∗ chainHash h1 xs h)


instance hashOf_persistent (d : List w8) (h : Hash) : Persistent (hashOf d h) := by
  unfold hashOf; infer_instance

instance chainHash_persistent (init : Hash) (P : List CmdId) (h : Hash) :
    Persistent (chainHash init P h) := by
  induction P generalizing init with
  | nil => unfold chainHash; infer_instance
  | cons x xs ih => unfold chainHash; infer_instance

/-- A hash has 32 bytes. -/
theorem hashOf_len (d : List w8) (h : Hash) : hashOf d h ⊢ ⌜h.length = 32⌝ := by
  unfold hashOf
  iintro ⟨%a, %Ha, H⟩
  ihave %Hl := sha256IsHash_len _ _ _ _ $$ H
  ipureintro; rw [← Ha]; exact Hl

/-- One input per hash seen (collision resistance). -/
theorem hashOf_inj (d1 d2 : List w8) (h : Hash) : hashOf d1 h ∗ hashOf d2 h ⊢ ⌜d1 = d2⌝ := by
  unfold hashOf
  iintro ⟨⟨%a1, %Ha1, H1⟩, ⟨%a2, %Ha2, H2⟩⟩
  have : a1 = a2 := by
    obtain ⟨l1⟩ := a1; obtain ⟨l2⟩ := a2; simp only at Ha1 Ha2; subst Ha1 Ha2; rfl
  subst this
  iapply sha256IsHash_inj _ netSha_noCollision _ _ _ _ $$ [$H1 $H2]

/-- A chain from a 32-byte start ends in 32 bytes. -/
theorem chainHash_len (init : Hash) (P : List CmdId) (h : Hash) (hi : init.length = 32) :
    chainHash init P h ⊢ ⌜h.length = 32⌝ := by
  induction P generalizing init with
  | nil => unfold chainHash; iintro %H; ipureintro; rw [H]; exact hi
  | cons x xs ih =>
    unfold chainHash
    iintro ⟨%h1, #H1, H⟩
    ihave %Hl := hashOf_len $$ H1
    iapply ih h1 Hl $$ H

/-- A chain's last round. -/
theorem chainHash_snoc (init : Hash) (P : List CmdId) (x : CmdId) (h : Hash) :
    chainHash init (P ++ [x]) h ⊣⊢ ∃ h1, chainHash init P h1 ∗ hashOf (h1 ++ encCmdId x) h := by
  induction P generalizing init with
  | nil =>
    simp only [List.nil_append]
    unfold chainHash chainHash
    constructor
    · iintro ⟨%h1, H1, %Hh⟩; subst Hh; iexists init; isplitr
      · ipureintro; rfl
      · iexact H1
    · iintro ⟨%h1, %Hh, H1⟩; subst Hh; iexists h; iframe H1; ipureintro; rfl
  | cons y ys ih =>
    simp only [List.cons_append]
    unfold chainHash
    constructor
    · iintro ⟨%h1, H1, H⟩
      ihave ⟨%h2, H2, H3⟩ := (ih h1).1 $$ H
      iexists h2; iframe H3; iexists h1; iframe
    · iintro ⟨%h2, ⟨%h1, H1, H2⟩, H3⟩
      iexists h1; iframe H1; iapply (ih h1).2; iexists h2; iframe

/-- **Two chains from the same 32-byte start to the same hash**: one path is a suffix of the
other. -/
theorem chainHash_suffix (init : Hash) (hi : init.length = 32) (P Q : List CmdId) (h : Hash) :
    chainHash init P h ∗ chainHash init Q h ⊢ ⌜P <:+ Q ∨ Q <:+ P⌝ := by
  induction P using snoc_induction generalizing Q h with
  | nil => iintro -; ipureintro; left; exact List.nil_suffix
  | snoc P x ih =>
    rcases eq_nil_or_snoc Q with rfl | ⟨Q', y, rfl⟩
    · iintro -; ipureintro; right; exact List.nil_suffix
    iintro ⟨HP, HQ⟩
    ihave ⟨%h1, H1, Hx⟩ := (chainHash_snoc init P x h).1 $$ HP
    ihave ⟨%h2, H2, Hy⟩ := (chainHash_snoc init Q' y h).1 $$ HQ
    ihave %Hl1 := chainHash_len init P h1 hi $$ H1
    ihave %Hl2 := chainHash_len init Q' h2 hi $$ H2
    ihave %Heq := hashOf_inj $$ [$Hx $Hy]
    have hh := List.append_inj Heq (by rw [Hl1, Hl2])
    obtain ⟨rfl, hxy⟩ := hh
    have := encCmdId_inj hxy; subst this
    ihave %Hs := ih Q' h1 $$ [$H1 $H2]
    ipureintro; exact suffix_snoc_or x Hs

/-! ## Start-marked path hashes (the code since F2's fix) -/

/-- `h` is the start-marked hash of the path `P` (`HashLog`'s, fork d9e184b): the first id alone
(`hashStart`), then each next id with the previous hash (`hash`). The empty path has none. -/
def startHash : List CmdId → Hash → IProp netDistGF
  | [], _ => iprop(False)
  | x :: xs, h => iprop(∃ h1, hashOf (encCmdId x) h1 ∗ chainHash h1 xs h)

instance startHash_persistent (P : List CmdId) (h : Hash) : Persistent (startHash P h) := by
  cases P <;> unfold startHash <;> infer_instance

theorem startHash_len (P : List CmdId) (h : Hash) : startHash P h ⊢ ⌜h.length = 32⌝ := by
  cases P with
  | nil => unfold startHash; iintro H; iexfalso; iexact H
  | cons x xs =>
    unfold startHash
    iintro ⟨%h1, #H1, H⟩
    ihave %Hl := hashOf_len $$ H1
    iapply chainHash_len h1 xs h Hl $$ H

theorem startHash_ne_nil (P : List CmdId) (h : Hash) : startHash P h ⊢ ⌜P ≠ []⌝ := by
  cases P with
  | nil => unfold startHash; iintro H; iexfalso; iexact H
  | cons x xs => iintro -; ipureintro; simp

/-- The path `[x]`: `hashStart(x)`. -/
theorem startHash_single (x : CmdId) (h : Hash) :
    hashOf (encCmdId x) h ⊢ startHash [x] h := by
  unfold startHash chainHash
  iintro #H; iexists h; iframe H; ipureintro; rfl

/-- One more id: `hash(h, x)`. -/
theorem startHash_snoc (P : List CmdId) (x : CmdId) (h h' : Hash) :
    startHash P h ∗ hashOf (h ++ encCmdId x) h' ⊢ startHash (P ++ [x]) h' := by
  cases P with
  | nil => unfold startHash; iintro ⟨H, -⟩; iexfalso; iexact H
  | cons y ys =>
    simp only [List.cons_append]
    unfold startHash
    iintro ⟨⟨%h1, H1, H⟩, Hx⟩
    iexists h1; iframe H1
    iapply (chainHash_snoc h1 ys x h').2
    iexists h; iframe

/-- The last round of a start-marked hash of a path of two ids or more. -/
theorem startHash_snoc_inv (P : List CmdId) (x : CmdId) (h : Hash) (hP : P ≠ []) :
    startHash (P ++ [x]) h ⊢ ∃ h1, startHash P h1 ∗ hashOf (h1 ++ encCmdId x) h := by
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hP
  simp only [List.cons_append]
  unfold startHash
  iintro ⟨%h1, H1, H⟩
  ihave ⟨%h2, H2, H3⟩ := (chainHash_snoc h1 ys x h).1 $$ H
  iexists h2; iframe H3; iexists h1; iframe

/-- The path `[x]`'s hash is `hashStart(x)`'s. -/
theorem startHash_one (x : CmdId) (h : Hash) : startHash [x] h ⊢ hashOf (encCmdId x) h := by
  unfold startHash chainHash
  iintro ⟨%h1, H1, %Hh⟩; subst Hh; iexact H1

/-- **Equal start-marked hashes are of equal paths** (the ideal hash: an 8-byte first round's
input is no 40-byte later round's). -/
theorem startHash_inj (P Q : List CmdId) (h : Hash) :
    startHash P h ∗ startHash Q h ⊢ ⌜P = Q⌝ := by
  induction P using snoc_induction generalizing Q h with
  | nil => unfold startHash; iintro ⟨H, -⟩; iexfalso; iexact H
  | snoc P x ih =>
    rcases eq_nil_or_snoc Q with rfl | ⟨Q', y, rfl⟩
    · unfold startHash; iintro ⟨-, H⟩; iexfalso; iexact H
    iintro ⟨HP, HQ⟩
    by_cases hP : P = [] <;> by_cases hQ : Q' = []
    · subst hP hQ
      simp only [List.nil_append]
      ihave Hx := startHash_one $$ HP
      ihave Hy := startHash_one $$ HQ
      ihave %Heq := hashOf_inj $$ [$Hx $Hy]
      ipureintro; rw [encCmdId_inj Heq]
    · subst hP
      simp only [List.nil_append]
      ihave Hx := startHash_one $$ HP
      ihave ⟨%h2, H2, Hy⟩ := startHash_snoc_inv Q' y h hQ $$ HQ
      ihave %Hl := startHash_len $$ H2
      ihave %Heq := hashOf_inj $$ [$Hx $Hy]
      have := congrArg List.length Heq
      simp [encCmdId_length, Hl] at this
    · subst hQ
      simp only [List.nil_append]
      ihave Hy := startHash_one $$ HQ
      ihave ⟨%h1, H1, Hx⟩ := startHash_snoc_inv P x h hP $$ HP
      ihave %Hl := startHash_len $$ H1
      ihave %Heq := hashOf_inj $$ [$Hx $Hy]
      have := congrArg List.length Heq
      simp [encCmdId_length, Hl] at this
    · ihave ⟨%h1, H1, Hx⟩ := startHash_snoc_inv P x h hP $$ HP
      ihave ⟨%h2, H2, Hy⟩ := startHash_snoc_inv Q' y h hQ $$ HQ
      ihave %Hl1 := startHash_len $$ H1
      ihave %Hl2 := startHash_len $$ H2
      ihave %Heq := hashOf_inj $$ [$Hx $Hy]
      obtain ⟨rfl, hxy⟩ := List.append_inj Heq (by rw [Hl1, Hl2])
      have := encCmdId_inj hxy; subst this
      ihave %Hs := ih Q' h1 $$ [$H1 $H2]
      ipureintro; rw [Hs]

/-- A start-marked hash equal to a chain from a 32-byte start: both paths non-empty, they end
with the same id. -/
theorem startHash_chain_last (init : Hash) (hi : init.length = 32) (P Q : List CmdId)
    (h : Hash) (hQ : Q ≠ []) :
    startHash P h ∗ chainHash init Q h ⊢ ⌜P.getLast? = Q.getLast?⌝ := by
  rcases eq_nil_or_snoc Q with rfl | ⟨Q', y, rfl⟩
  · exact absurd rfl hQ
  rcases eq_nil_or_snoc P with rfl | ⟨P', x, rfl⟩
  · unfold startHash; iintro ⟨H, -⟩; iexfalso; iexact H
  iintro ⟨HP, HQ⟩
  ihave ⟨%h2, H2, Hy⟩ := (chainHash_snoc init Q' y h).1 $$ HQ
  ihave %Hl2 := chainHash_len init Q' h2 hi $$ H2
  by_cases hP : P' = []
  · subst hP
    simp only [List.nil_append]
    ihave Hx := startHash_one $$ HP
    ihave %Heq := hashOf_inj $$ [$Hx $Hy]
    have := congrArg List.length Heq
    simp [encCmdId_length, Hl2] at this
  · ihave ⟨%h1, H1, Hx⟩ := startHash_snoc_inv P' x h hP $$ HP
    ihave %Hl1 := startHash_len $$ H1
    ihave %Heq := hashOf_inj $$ [$Hx $Hy]
    obtain ⟨-, hxy⟩ := List.append_inj Heq (by rw [Hl1, Hl2])
    have := encCmdId_inj hxy; subst this
    ipureintro; simp

/-! ## The checksums -/

/-- The hashes `hs` of the dependency paths `Ps` (`HashLog`'s): each the start-marked hash of a
path (`startHash`, F2's fix), whose last id is a client's (its client id is not `-1`).
(change log C9: start-marked, was the chain from the zero hash) -/
def pathHashes (Ps : List (List CmdId)) (hs : List Hash) : IProp netDistGF :=
  iprop(⌜hs.length = Ps.length ∧ ∀ P ∈ Ps, ∃ P' x, P = P' ++ [x] ∧ x.cl ≠ -1⌝ ∗
    [∗list] i ↦ P ∈ Ps, ∃ h, ⌜hs[i]? = some h⌝ ∗ startHash P h)

/-- The dependencies' hash of `clientChecksum`: the sorted ids chained from the zero hash, then
one round over the id `(-1, length)`. -/
def depHash (D : List CmdId) (h : Hash) : IProp netDistGF :=
  chainHash (List.replicate 32 (W8 0)) (sortIds D ++ [⟨-1, W32 (D.length : Int)⟩]) h

/-- `cs` is `clientChecksum(hs, D)`: the hashes of the paths `Ps`, then the dependencies'
hash. -/
def checksum (Ps : List (List CmdId)) (D : List CmdId) (cs : List Hash) : IProp netDistGF :=
  iprop(∃ hs d, ⌜cs = hs ++ [d]⌝ ∗ pathHashes Ps hs ∗ depHash D d)

/-- `SHashesEq` (`swift/dpath.go`): the same length, every hash of the first in the second. -/
def shashesEq (hs1 hs2 : List Hash) : Prop := hs1.length = hs2.length ∧ ∀ h ∈ hs1, h ∈ hs2


/-! ## The checksums' laws -/

instance pathHashes_persistent (Ps : List (List CmdId)) (hs : List Hash) :
    Persistent (pathHashes Ps hs) := by unfold pathHashes; infer_instance
instance depHash_persistent (D : List CmdId) (h : Hash) : Persistent (depHash D h) := by
  unfold depHash; infer_instance
instance checksum_persistent (Ps : List (List CmdId)) (D : List CmdId) (cs : List Hash) :
    Persistent (checksum Ps D cs) := by
  unfold checksum; infer_instance

theorem pathHashes_len (Ps : List (List CmdId)) (hs : List Hash) :
    pathHashes Ps hs ⊢ ⌜hs.length = Ps.length⌝ := by
  unfold pathHashes; iintro ⟨%Hok, -⟩; ipureintro; exact Hok.1

theorem pathHashes_lookup (Ps : List (List CmdId)) (hs : List Hash) (i : Nat) (h : Hash)
    (hi : hs[i]? = some h) :
    pathHashes Ps hs ⊢ ∃ P, ⌜Ps[i]? = some P ∧ ∃ P' x, P = P' ++ [x] ∧ x.cl ≠ -1⌝ ∗
      startHash P h := by
  unfold pathHashes
  iintro ⟨%Hok, Hl⟩
  obtain ⟨hlen, hall⟩ := Hok
  have hi' : i < Ps.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨P, hP⟩ : ∃ P, Ps[i]? = some P := ⟨Ps[i], List.getElem?_eq_getElem hi'⟩
  ihave ⟨%h', %Hh', Hc⟩ := (BigSepL.bigSepL_lookup hP) $$ Hl
  rw [hi] at Hh'; cases Hh'
  iexists P; iframe Hc; ipureintro
  exact ⟨hP, hall P (List.mem_of_getElem? hP)⟩

theorem pathHashes_one (P : List CmdId) (hs : List Hash) :
    pathHashes [P] hs ⊢ ∃ h, ⌜hs = [h] ∧ ∃ P' x, P = P' ++ [x] ∧ x.cl ≠ -1⌝ ∗ startHash P h := by
  iintro #H
  ihave %Hl := pathHashes_len $$ H
  obtain ⟨h, rfl⟩ : ∃ h, hs = [h] := by
    match hs, Hl with
    | [h], _ => exact ⟨h, rfl⟩
  ihave ⟨%P0, %HP, Hc⟩ := pathHashes_lookup [P] [h] 0 h rfl $$ H
  obtain ⟨hP0, hlast⟩ := HP
  simp at hP0; subst hP0
  iexists h; iframe Hc; ipureintro; exact ⟨rfl, hlast⟩

/-- A start-marked path hash is no dependency hash. -/
theorem startHash_ne_depHash (P D : List CmdId) (h : Hash)
    (hP : ∃ P' x, P = P' ++ [x] ∧ x.cl ≠ -1) :
    startHash P h ∗ depHash D h ⊢ False := by
  unfold depHash
  iintro ⟨H1, H2⟩
  ihave %Hl := startHash_chain_last zeroHash (by simp) _ _ h (by simp) $$ [$H1 $H2]
  obtain ⟨P', x, rfl, hx⟩ := hP
  exfalso; simp at Hl; exact hx (by simp [Hl])

/-- Two equal dependency hashes of lists shorter than `2^32` are of permuted lists (the length
round hashes `int32(len)`). -/
theorem depHash_perm (D1 D2 : List CmdId) (d : Hash)
    (hb : D1.length < 2 ^ 32 ∧ D2.length < 2 ^ 32) :
    depHash D1 d ∗ depHash D2 d ⊢ ⌜D1.Perm D2⌝ := by
  unfold depHash
  iintro ⟨Hd1, Hd2⟩
  ihave %Hs := chainHash_suffix zeroHash (by simp) _ _ d $$ [$Hd1 $Hd2]
  ipureintro
  have hl : (sortIds D1 ++ [⟨-1, W32 (D1.length : Int)⟩] : List CmdId).getLast? =
      (sortIds D2 ++ [⟨-1, W32 (D2.length : Int)⟩] : List CmdId).getLast? := by
    rcases Hs with Hs | Hs
    · exact suffix_getLast? Hs (by simp)
    · exact (suffix_getLast? Hs (by simp)).symm
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq, CmdId.mk.injEq, true_and] at hl
  have hlen : D1.length = D2.length := by
    have := congrArg BitVec.toNat hl
    simp at this
    omega
  have hsl : (sortIds D1).length = (sortIds D2).length := by simp [sortIds, hlen]
  have heq : sortIds D1 ++ [⟨-1, W32 (D1.length : Int)⟩] =
      sortIds D2 ++ [⟨-1, W32 (D2.length : Int)⟩] := by
    rcases Hs with Hs | Hs
    · exact Hs.eq_of_length (by simp [hsl])
    · exact (Hs.eq_of_length (by simp [hsl])).symm
  have h' := List.append_inj_left' heq rfl
  unfold sortIds at h'
  exact (List.mergeSort_perm D1 _).symm.trans (by rw [h']; exact List.mergeSort_perm D2 _)

/-- **Equal single-path checksums are of equal paths** (`Inv.lean`'s `checksum_path`). -/
theorem checksum_path_eq (P1 P2 D1 D2 : List CmdId) (cs1 cs2 : List Hash) :
    checksum [P1] D1 cs1 ∗ checksum [P2] D2 cs2 ∗ ⌜shashesEq cs1 cs2⌝ ⊢ ⌜P1 = P2⌝ := by
  unfold checksum
  iintro ⟨⟨%hs1, %d1, %Hc1, Hp1, -⟩, ⟨%hs2, %d2, %Hc2, Hp2, Hd2⟩, %Heq⟩
  ihave ⟨%h1, %H1, Hch1⟩ := pathHashes_one $$ Hp1
  ihave ⟨%h2, %H2, Hch2⟩ := pathHashes_one $$ Hp2
  obtain ⟨rfl, hlast1⟩ := H1
  obtain ⟨rfl, -⟩ := H2
  subst Hc1 Hc2
  have hm : h1 ∈ [h2, d2] := Heq.2 h1 (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · iapply startHash_inj $$ [$Hch1 $Hch2]
  · iexfalso
    iapply startHash_ne_depHash P1 D2 h1 hlast1 $$ [$Hch1 $Hd2]

/-- **Equal checksums have permuted dependencies** (lengths < 2^32; `Inv.lean`'s
`checksum_deps`). -/
theorem checksum_deps_perm (Ps1 Ps2 : List (List CmdId)) (D1 D2 : List CmdId)
    (cs1 cs2 : List Hash) (hb : D1.length < 2 ^ 32 ∧ D2.length < 2 ^ 32) :
    checksum Ps1 D1 cs1 ∗ checksum Ps2 D2 cs2 ∗ ⌜shashesEq cs1 cs2⌝ ⊢ ⌜D1.Perm D2⌝ := by
  unfold checksum
  iintro ⟨⟨%hs1, %d1, %Hc1, -, Hd1⟩, ⟨%hs2, %d2, %Hc2, Hp2, Hd2⟩, %Heq⟩
  subst Hc1 Hc2
  have hm : d1 ∈ hs2 ++ [d2] := Heq.2 d1 (by simp)
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
    ihave ⟨%P, %HP, Hc⟩ := pathHashes_lookup Ps2 hs2 i d1 hi $$ Hp2
    iexfalso
    iapply startHash_ne_depHash P D1 d1 HP.2 $$ [$Hc $Hd1]
  simp only [List.mem_singleton] at hm; subst hm
  iapply depHash_perm D1 D2 d1 hb $$ [$Hd1 $Hd2]

end ghost

section node
variable [GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
  [crypto.sha256.Assumptions]

/-- At a node, Perennial's `is_hash` (`crypto.sha256.wp_Sum256`'s postcondition) is `hashOf` at
the node's global ghost state. -/
theorem hashOf_of_is_hash (d : List w8) (h : GoArray w8 32) :
    crypto.sha256.is_hash (GF := netDistGF) d h ⊢ hashOf d h.arr := by
  unfold hashOf crypto.sha256.is_hash
  iintro H; iexists h; isplitl []
  · ipureintro; rfl
  iexact H

end node

end sp

end Perennial.github_com.imdea_software.swiftpaxos
