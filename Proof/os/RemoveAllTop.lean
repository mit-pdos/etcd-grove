/-
The pieces of `os.RemoveAll`'s top-level proofs that more than one proof uses (`Proof/os/RemoveAll.lean`,
`Proof/os/RemoveAllSub.lean`): the root's form of a spine's path, a model error pointer as an `error`
`fmt` formats, the call permission's halves. Moved from `RemoveAll.lean` (import tiers: a proof imports no
proof). Lean-first; untrusted.
-/
module

public import Proof.os.RemoveAllFrom

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- A path of the roots begins with a separator followed by a byte that is not one. -/
theorem os.root_path_head {R : Roots} {r : GoString} {j0 : Ino} {cs : List GoString}
    (hR : RootsOk R) (hm : (r, j0) ∈ R) :
    ∃ c rest, joinPath r cs = slashB :: c :: rest ∧ c ≠ slashB := by
  obtain ⟨⟨cs', hne, hok, hr⟩, -⟩ := hR.2.2 (r, j0) hm
  obtain ⟨c1, cs'', rfl⟩ : ∃ c1 cs'', cs' = c1 :: cs'' := by
    cases cs' with
    | nil => exact absurd rfl hne
    | cons c1 cs'' => exact ⟨c1, cs'', rfl⟩
  obtain ⟨hc1, -, -, hs1, -⟩ := hok c1 (by simp)
  obtain ⟨x, xs, rfl⟩ : ∃ x xs, c1 = x :: xs := by
    cases c1 with
    | nil => exact absurd rfl hc1
    | cons x xs => exact ⟨x, xs, rfl⟩
  refine ⟨x, xs ++ cs''.flatMap (fun c => slashB :: c) ++ cs.flatMap (fun c => slashB :: c), ?_,
    fun h => hs1 (by simp [h])⟩
  simp only at hr
  rw [hr]
  simp [joinPath]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.fileStat.FieldAssumptions]

/-- What a spine says of its path: the root's form, and `TreePath`'s for `d/b`. -/
theorem os.osPathS_facts (R : Roots) (d : GoString) (dq : DFrac) (j : Ino) (b : GoString)
    (hb : NameOk b) :
    osPathS (GF := GF) R d dq j ⊢ ⌜(∃ c rest, d = slashB :: c :: rest ∧ c ≠ slashB) ∧
      ∃ r j0 cs, (r, j0) ∈ R ∧ (∀ c ∈ cs, NameOk c) ∧ child d b = joinPath r cs⌝ := by
  unfold osPathS
  iintro ⟨%r, %j0, %cs, %hp, -⟩
  obtain ⟨hR, hm, hcs, rfl⟩ := hp
  ipureintro
  refine ⟨os.root_path_head hR hm, r, j0, cs ++ [b], hm, ?_, (joinPath_snoc r cs b).symm⟩
  intro c hc; simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact hcs c hc
  · exact hb

/-- A non-nil error pointer of `RemoveAll`'s model, as an `error`, is one `fmt` formats. -/
theorem os.peOk_fmt (pe : Loc) (hpn : pe ≠ null) :
    os.peOk (GF := GF) pe ⊢ |==> fmtErrorOkOrNil
      (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe) := by
  unfold os.peOk
  iintro (%hn | ⟨%op, %path, %err, #Hop, Hpath, #Herr, #Hok⟩)
  · exact absurd hn hpn
  ipersist Hpath
  imodintro
  iapply (EtcdGrove.fmtErrorOkOrNil_of _)
  iapply (os.pathError_fmtErrorOk pe op path err) $$ Hop Hpath Herr Hok

/-- The call permission's two halves. -/
theorem os.osCallPerm_halves (r : GoString) (q : Qp) :
    osCallPerm (GF := GF) r q.half ∗ osCallPerm r q.half ⊣⊢ osCallPerm r q := by
  have h := osCallPerm_split (GF := GF) r q.half q.half
  rw [Qp.half_add_half] at h
  exact ⟨h.2, h.1⟩

end proof

end EtcdGrove
end Perennial

end
