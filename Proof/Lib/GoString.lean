/-
Facts about Perennial's order on Go strings (`go.GoStringLt`, the lexicographic order on bytes)
that belong to no Go package: it is a strict total order. Each is Lean core's fact about
`List.Lex` at `GoStringLt`.

They are kept here until Perennial has them: each is a candidate for an independent Perennial
proposal (CLAUDE.md, "Changes to Perennial"), and goes once its Perennial counterpart lands
(`notes/decisions.md`, "Proof/Lib: facts that belong to no Go package").
-/
module

public import Perennial.Golang.Defn.String

@[expose] public section

namespace Perennial
namespace EtcdGrove

theorem goStringLt_irrefl (a : GoString) : ¬ go.GoStringLt a a :=
  List.lex_irrefl (r := fun (x y : w8) => uint.Z x < uint.Z y) (fun _ => Int.lt_irrefl _) a

theorem goStringLt_trans {a b c : GoString} (h1 : go.GoStringLt a b) (h2 : go.GoStringLt b c) :
    go.GoStringLt a c :=
  List.lex_trans (r := fun (x y : w8) => uint.Z x < uint.Z y) (fun h h' => Int.lt_trans h h') h1 h2

theorem goStringLt_asymm {a b : GoString} (h : go.GoStringLt a b) : ¬ go.GoStringLt b a :=
  List.lex_asymm (r := fun (x y : w8) => uint.Z x < uint.Z y) (fun h h' => Int.lt_asymm h h') h

/-- Go's `<` on strings is total. -/
theorem goStringLt_eq_of_not_lt {a b : GoString} (h1 : ¬ go.GoStringLt a b)
    (h2 : ¬ go.GoStringLt b a) : a = b :=
  List.lex_trichotomous (r := fun (x y : w8) => uint.Z x < uint.Z y) (fun x y a1 a2 => by
    apply BitVec.eq_of_toNat_eq
    simp only [uint.Z] at a1 a2
    omega) h2 h1

end EtcdGrove
end Perennial
