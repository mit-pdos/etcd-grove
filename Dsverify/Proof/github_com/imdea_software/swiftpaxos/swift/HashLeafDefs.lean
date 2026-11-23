/-
The definitions, specs and lemmas of `HashLeaf.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ChainHash
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Marshal
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.swift

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift

/-- A Go `CommandId` as the wire's. -/
def toCmdId (x : swift.CommandId) : sp.CmdId := ⟨x.ClientId', x.SeqNum'⟩

/-- A Go `CommandId` from the wire's. -/
def ofCmdId (x : sp.CmdId) : swift.CommandId := ⟨x.cl, x.seq⟩

@[simp] theorem toCmdId_ofCmdId (x : sp.CmdId) : toCmdId (ofCmdId x) = x := rfl
@[simp] theorem ofCmdId_toCmdId (x : swift.CommandId) : ofCmdId (toCmdId x) = x := rfl

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- `putId(bs, x)`: `bs`'s first 8 bytes become `x`'s encoding. -/
abbrev putId.spec : Prop :=
  ∀ (bs : GoSlice) (old rest : List w8) (x : swift.CommandId),
  {{ (bs ↦* (old ++ rest) : IProp netDistGF) ∗ ⌜old.length = 8⌝ }}
    (App (App (Val (@! swift.putId)) (Val #bs)) (Val #x))
  {{ RET #(); bs ↦* (sp.encCmdId (toCmdId x) ++ rest) }}

/-- `hashStart(x)`: the hash of the path `[x]`'s round, over the id's 8 bytes. -/
abbrev hashStart.spec : Prop :=
  ∀ (x : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.crypto.sha256 }}
    (App (Val (@! swift.hashStart)) (Val #x))
  {{ (h : GoArray w8 32), RET #h; sp.hashOf (sp.encCmdId (toCmdId x)) h.arr }}

/-- `hash(initial, x)`: the round over `initial`'s 32 bytes and the id's 8. -/
abbrev hash.spec : Prop :=
  ∀ (initial : GoArray w8 32) (x : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.crypto.sha256 ∗ ⌜initial.arr.length = 32⌝ }}
    (App (App (Val (@! swift.hash)) (Val #initial)) (Val #x))
  {{ (h : GoArray w8 32), RET #h; sp.hashOf (initial.arr ++ sp.encCmdId (toCmdId x)) h.arr }}

/-- `l.chain(h, started, x)`: `hash(h, x)` if `started`, else `hashStart(x)`. -/
abbrev HashLog.chain.spec : Prop :=
  ∀ (l : Loc) (h : GoArray w8 32) (started : Bool) (x : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.crypto.sha256 ∗ ⌜h.arr.length = 32⌝ }}
    (App (App (App (Val (l @!! go.GoType.PointerType swift.HashLog.ty @!! go!"chain"))
      (Val #h)) (Val #started)) (Val #x))
  {{ (h' : GoArray w8 32), RET #h';
      sp.hashOf ((if started then h.arr else []) ++ sp.encCmdId (toCmdId x)) h'.arr }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

set_option goose.wp.extras true

theorem set8_app {A : Type} (l rest : List A) (hl : l.length = 8) (a b c d e f g h : A) :
    ((((((((l ++ rest).set 0 a).set 1 b).set 2 c).set 3 d).set 4 e).set 5 f).set 6 g).set 7 h =
      [a, b, c, d, e, f, g, h] ++ rest := by
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem set_take_rep {A : Type} (l : List A) (z : A) (k : Nat) (hk : k < l.length) (n : Nat) (hn : k < n) :
    (l.take k ++ List.replicate (n - k) z).set k l[k] = l.take (k + 1) ++ List.replicate (n - (k + 1)) z := by
  have hl : (l.take k).length = k := by rw [List.length_take]; omega
  rw [List.set_append_right _ _ (by omega), hl, Nat.sub_self]
  obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
  rw [hm, List.replicate_succ, List.set_cons_zero, List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.append_assoc, List.cons_append, List.nil_append]
  rw [show n - (k + 1) = m by omega]

set_option hygiene false in
/-- One store `bs[i] = x` into the buffer `Hsl` (the bounds check first). -/
local macro "store8" : tactic => `(tactic| (
  (try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)])
  wp_pures
  wp_apply wp_store_slice_index _ _ _ _ $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro
    simp only [List.length_set, List.length_append, Hold]
    word
  (try wp_auto)))

end proofs

end swift

end Perennial.github_com.imdea_software.swiftpaxos
