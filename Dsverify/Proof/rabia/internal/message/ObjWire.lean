/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/ObjWire.lean`, run `rabia-r1wake-1`.)

`ConsensusObj`'s and `Command`'s encodings as lists of segments (one per field, one per
command), and the records decoded so far (`ObjV.upto`, `CmdV.upto`), for the `Unmarshal` loops
(prover C1).
-/
module

public import Dsverify.Proof.rabia.internal.message.MsgWire

@[expose] public section

namespace Perennial.rabia.model

/-! ## ConsensusObj -/

/-- The segments of `encObj o`: fields 1..6, then one per command. -/
def objSegs (o : ObjV) : List (List w8) :=
  [encScalar 0x08 o.proId.toNat, encScalar 0x10 o.proSeq.toNat, encScalar 0x18 o.svrSeq.toNat,
   (if o.isNull then [0x20, 1] else []), encPacked 0x2a o.cliIds, encPacked 0x32 o.cliSeqs] ++
  o.commands.map (encBytes 0x3a)

theorem objSegs_length (o : ObjV) : (objSegs o).length = 6 + o.commands.length := by
  simp [objSegs]; omega

theorem encObj_flatten (o : ObjV) : encObj o = (objSegs o).flatten := by
  unfold encObj objSegs
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.append_assoc]
  rfl

/-- The fields before `s` of `o` (the commands: the first `s - 6`), the others zero. -/
def ObjV.upto (o : ObjV) (s : Nat) : ObjV :=
  { proId := if 0 < s then o.proId else 0, proSeq := if 1 < s then o.proSeq else 0,
    svrSeq := if 2 < s then o.svrSeq else 0, isNull := if 3 < s then o.isNull else false,
    cliIds := if 4 < s then o.cliIds else [], cliSeqs := if 5 < s then o.cliSeqs else [],
    commands := o.commands.take (s - 6) }

theorem ObjV.upto_all (o : ObjV) : o.upto (6 + o.commands.length) = o := by
  simp only [ObjV.upto]
  rcases o with ⟨a, b, c, d, e, f, g⟩
  simp only [ObjV.mk.injEq]
  simp only [show 0 < 6 + g.length by omega, show 1 < 6 + g.length by omega,
    show 2 < 6 + g.length by omega, show 3 < 6 + g.length by omega, show 4 < 6 + g.length by omega,
    show 5 < 6 + g.length by omega, ite_true, show 6 + g.length - 6 = g.length by omega,
    List.take_length, and_self]

theorem encPacked_eq_nil {t : w8} {ns : List w32} : encPacked t ns = [] ↔ ns = [] := by
  unfold encPacked encBytes; by_cases h : ns = [] <;> simp [h]

theorem ObjV.upto_succ (o : ObjV) (i : Nat) (hi : i < 6 + o.commands.length)
    (h : (objSegs o)[i]? = some []) : o.upto (i + 1) = o.upto i := by
  rcases o with ⟨a, b, c, d, e, f, g⟩
  by_cases h6 : i < 6
  · have hcmd : i + 1 - 6 = i - 6 := by omega
    match i, h6 with
    | 0, _ =>
      simp [objSegs, encScalar_eq_nil] at h
      simp only [ObjV.upto, hcmd]; simp; apply BitVec.eq_of_toNat_eq; simpa using h
    | 1, _ =>
      simp [objSegs, encScalar_eq_nil] at h
      simp only [ObjV.upto, hcmd]; simp; apply BitVec.eq_of_toNat_eq; simpa using h
    | 2, _ =>
      simp [objSegs, encScalar_eq_nil] at h
      simp only [ObjV.upto, hcmd]; simp; apply BitVec.eq_of_toNat_eq; simpa using h
    | 3, _ =>
      simp [objSegs] at h
      simp only [ObjV.upto, hcmd]; simp [h]
    | 4, _ =>
      simp [objSegs, encPacked_eq_nil] at h
      simp only [ObjV.upto, hcmd]; simp [h]
    | 5, _ =>
      simp [objSegs, encPacked_eq_nil] at h
      simp only [ObjV.upto, hcmd]; simp [h]
  · exfalso
    simp only [objSegs, List.getElem?_append_right (by simp; omega : [encScalar 0x08 a.toNat, encScalar 0x10 b.toNat, encScalar 0x18 c.toNat,
      (if d then [0x20, 1] else []), encPacked 0x2a e, encPacked 0x32 f].length ≤ i)] at h
    simp [encBytes] at h

theorem ObjV.upto_of_empty (o : ObjV) (s j : Nat) (hsj : s ≤ j) (hj : j ≤ 6 + o.commands.length)
    (h : ∀ i, s ≤ i → i < j → (objSegs o)[i]? = some []) : o.upto j = o.upto s := by
  induction j with
  | zero => have : s = 0 := by omega
            subst this; rfl
  | succ j ih =>
    by_cases hs : s = j + 1
    · subst hs; rfl
    · rw [o.upto_succ j (by omega) (h j (by omega) (by omega))]
      exact ih (by omega) (by omega) (fun i h1 h2 => h i h1 (by omega))

/-! ## Command -/

/-- The segments of `encCmd c`: fields 1..3, then one per command. -/
def cmdSegs (c : CmdV) : List (List w8) :=
  [encScalar 0x08 c.cliId.toNat, encScalar 0x10 c.cliSeq.toNat, encScalar 0x18 c.svrSeq.toNat] ++
  c.commands.map (encBytes 0x22)

theorem cmdSegs_length (c : CmdV) : (cmdSegs c).length = 3 + c.commands.length := by
  simp [cmdSegs]; omega

theorem encCmd_flatten (c : CmdV) : encCmd c = (cmdSegs c).flatten := by
  unfold encCmd cmdSegs
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.append_assoc]
  rfl

def CmdV.upto (c : CmdV) (s : Nat) : CmdV :=
  { cliId := if 0 < s then c.cliId else 0, cliSeq := if 1 < s then c.cliSeq else 0,
    svrSeq := if 2 < s then c.svrSeq else 0, commands := c.commands.take (s - 3) }

theorem CmdV.upto_all (c : CmdV) : c.upto (3 + c.commands.length) = c := by
  simp only [CmdV.upto]
  rcases c with ⟨a, b, d, g⟩
  simp only [CmdV.mk.injEq]
  simp only [show 0 < 3 + g.length by omega, show 1 < 3 + g.length by omega,
    show 2 < 3 + g.length by omega, ite_true, show 3 + g.length - 3 = g.length by omega,
    List.take_length, and_self]

theorem CmdV.upto_succ (c : CmdV) (i : Nat) (hi : i < 3 + c.commands.length)
    (h : (cmdSegs c)[i]? = some []) : c.upto (i + 1) = c.upto i := by
  rcases c with ⟨a, b, d, g⟩
  by_cases h3 : i < 3
  · have hcmd : i + 1 - 3 = i - 3 := by omega
    match i, h3 with
    | 0, _ =>
      simp [cmdSegs, encScalar_eq_nil] at h
      simp only [CmdV.upto, hcmd]; simp; apply BitVec.eq_of_toNat_eq; simpa using h
    | 1, _ =>
      simp [cmdSegs, encScalar_eq_nil] at h
      simp only [CmdV.upto, hcmd]; simp; apply BitVec.eq_of_toNat_eq; simpa using h
    | 2, _ =>
      simp [cmdSegs, encScalar_eq_nil] at h
      simp only [CmdV.upto, hcmd]; simp; apply BitVec.eq_of_toNat_eq; simpa using h
  · exfalso
    simp only [cmdSegs, List.getElem?_append_right (by simp; omega : [encScalar 0x08 a.toNat,
      encScalar 0x10 b.toNat, encScalar 0x18 d.toNat].length ≤ i)] at h
    simp [encBytes] at h

theorem CmdV.upto_of_empty (c : CmdV) (s j : Nat) (hsj : s ≤ j) (hj : j ≤ 3 + c.commands.length)
    (h : ∀ i, s ≤ i → i < j → (cmdSegs c)[i]? = some []) : c.upto j = c.upto s := by
  induction j with
  | zero => have : s = 0 := by omega
            subst this; rfl
  | succ j ih =>
    by_cases hs : s = j + 1
    · subst hs; rfl
    · rw [c.upto_succ j (by omega) (h j (by omega) (by omega))]
      exact ih (by omega) (by omega) (fun i h1 h2 => h i h1 (by omega))

end Perennial.rabia.model
