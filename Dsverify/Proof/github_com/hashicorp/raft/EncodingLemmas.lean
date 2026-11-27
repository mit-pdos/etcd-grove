/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/EncodingLemmas.lean (241f27e).
-/
/-
Pure lemmas about `le64` and `encodeServers` (encoding.go), shared by the proofs of the encoding
helpers, `EncodeConfiguration`, `DecodeConfiguration`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Defs

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

theorem W8_uintZ (y : w64) : W8 (uint.Z y) = y.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [W8, uint.Z]

theorem shiftr_mul8 (x k : w64) (h : uint.Z k < 8) : x >>> (W64 8 * k) = x >>> (8 * k.toNat) := by
  change x >>> (W64 8 * k).toNat = _
  congr 1
  simp [uint.Z] at h
  simp [BitVec.toNat_mul]; omega

theorem shiftl_mul8 (x k : w64) (h : uint.Z k < 8) : x <<< (W64 8 * k) = x <<< (8 * k.toNat) := by
  change x <<< (W64 8 * k).toNat = _
  congr 1
  simp [uint.Z] at h
  simp [BitVec.toNat_mul]; omega

theorem W64_uintZ_w8 (z : w8) : W64 (uint.Z z) = z.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [W64, uint.Z]

theorem le64_length (x : w64) : (le64 x).length = 8 := by simp [le64]

theorem le64_getElem (x : w64) (n : Nat) (h : n < 8) :
    (le64 x)[n]? = some ((x >>> (8 * n)).setWidth 8) := by
  simp [le64, h]

theorem le64_take_succ (x : w64) (n : Nat) (h : n < 8) :
    (le64 x).take (n + 1) = (le64 x).take n ++ [(x >>> (8 * n)).setWidth 8] := by
  rw [List.take_succ, le64_getElem x n h]; rfl

theorem le64_take_8 (x : w64) : (le64 x).take 8 = le64 x := by
  rw [List.take_of_length_le]; simp [le64_length]

/-- The mask of the low `8 k` bits. -/
def lowMask (k : Nat) : w64 := BitVec.allOnes 64 >>> (64 - 8 * k)

theorem lowMask_0 : lowMask 0 = 0 := by decide
theorem lowMask_8 (x : w64) : x &&& lowMask 8 = x := by
  -- (port) was `bv_decide`, whose certificate adds `Lean.ofReduceBool`: `lowMask 8` is all ones
  unfold lowMask; simp only [Nat.reduceMul, Nat.sub_self, BitVec.ushiftRight_zero]
  exact BitVec.and_allOnes

theorem lowMask_succ (x : w64) (k : Nat) (h : k < 8) :
    (x &&& lowMask k) ||| (((x >>> (8 * k)).setWidth 8).setWidth 64 <<< (8 * k)) =
      x &&& lowMask (k + 1) := by
  -- bitwise (no `bv_decide`: its SAT certificates add `_native` axioms to the results)
  unfold lowMask
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_ushiftRight,
    BitVec.getElem_shiftLeft, BitVec.getElem_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h1 : i < 8 * k
  · have : 64 - 8 * k + i < 64 := by omega
    have : 64 - 8 * (k + 1) + i < 64 := by omega
    simp [*]
  · by_cases h2 : i < 8 * (k + 1)
    · have : ¬ 64 - 8 * k + i < 64 := by omega
      have : 64 - 8 * (k + 1) + i < 64 := by omega
      have : i - 8 * k < 8 := by omega
      have : 8 * k + (i - 8 * k) = i := by omega
      simp [*]
    · have : ¬ 64 - 8 * k + i < 64 := by omega
      have : ¬ 64 - 8 * (k + 1) + i < 64 := by omega
      have : ¬ i - 8 * k < 8 := by omega
      simp [*]

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- The package's globals from `isPkgInit`. -/
theorem pkgGlobals_of_isPkgInit :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ⊢ pkgGlobals (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.github_com.hashicorp.raft

end init

section srv
variable [GooseExts]

/-- The encoding of one server. -/
def encSrv (s : Server) : List w8 :=
  le64 s.Suffrage' ++ le64 (W64 s.ID'.length) ++ s.ID' ++ le64 (W64 s.Address'.length) ++ s.Address'

theorem encodeServers_eq (ss : List Server) :
    encodeServers ss = le64 (W64 ss.length) ++ ss.flatMap encSrv := rfl

theorem flatMap_take_succ {A B : Type} (f : A → List B) (l : List A) (k : Nat) (a : A)
    (h : l[k]? = some a) :
    (l.take (k + 1)).flatMap f = (l.take k).flatMap f ++ f a := by
  rw [List.take_succ, h]; simp

theorem encSrv_length_pos (s : Server) : 0 < (encSrv s).length := by
  simp [encSrv, le64_length]; omega

theorem length_le_flatMap_encSrv (ss : List Server) : ss.length ≤ (ss.flatMap encSrv).length := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := encSrv_length_pos s
    omega

theorem drop_flatMap_encSrv (ss : List Server) (k : Nat) (sv : Server) (h : ss[k]? = some sv) :
    (ss.drop k).flatMap encSrv =
      le64 sv.Suffrage' ++ ((le64 (W64 sv.ID'.length) ++ sv.ID') ++
        ((le64 (W64 sv.Address'.length) ++ sv.Address') ++ (ss.drop (k + 1)).flatMap encSrv)) := by
  obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hk, he]
  simp [encSrv, List.append_assoc]

/-- The set of keys `f s` of the servers `l`, as a map to `true` (`checkConfiguration`'s sets). -/
def keySet (f : Server → GoString) (l : List Server) : GMap GoString Bool :=
  l.foldl (fun m s => GMap.insert (f s) true m) ∅

theorem keySet_snoc (f : Server → GoString) (l : List Server) (s : Server) :
    keySet f (l ++ [s]) = GMap.insert (f s) true (keySet f l) := by
  simp [keySet, List.foldl_append]

theorem keySet_lookup_none (f : Server → GoString) (l : List Server) (x : GoString)
    (h : x ∉ l.map f) : keySet f l !! x = none := by
  unfold keySet
  suffices ∀ m : GMap GoString Bool, m !! x = none →
      (l.foldl (fun m s => GMap.insert (f s) true m) m) !! x = none from this ∅ rfl
  induction l with
  | nil => intro m hm; exact hm
  | cons a l ih =>
    intro m hm
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    apply ih h.2
    rw [GMap.lookup_insert_None]
    exact ⟨hm, fun e => h.1 e.symm⟩

theorem nodup_take_not_mem {A B : Type} (f : A → B) (l : List A) (k : Nat) (a : A)
    (hnd : (l.map f).Nodup) (h : l[k]? = some a) : f a ∉ (l.take k).map f := by
  intro hm
  have e : l.map f = (l.take k).map f ++ (l.drop k).map f := by
    rw [← List.map_append, List.take_append_drop]
  rw [e] at hnd
  have hd := (List.nodup_append.mp hnd).2.2
  obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp h
  have hm2 : f a ∈ (l.drop k).map f := by
    rw [List.drop_eq_getElem_cons hk, he]; simp
  exact hd _ hm _ hm2 rfl

end srv

end github_com.hashicorp.raft

end Perennial
