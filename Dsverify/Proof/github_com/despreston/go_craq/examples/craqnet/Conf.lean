/-
The craq kit's configuration messages (`kit.go`'s `Conf`, `removal`, `msg`, `decode`; lab
`Kit/Iface.lean`, notes/dsv-craq.md, P4 (c)): pure definitions.

* `confOk`: a configuration `decode` accepts (and `choose` picks): a chain of 3 to `MaxChain` = 5
  nodes, at most 2 of them late, a read mode 0 or 1.
* `remOk conf r`: a removal `decode` accepts for `conf`: of a chain node `2..N+1`, after `1..K-1`
  (`K` = 6) operations; `remsOk conf rs`: at most `MaxRemovals` = 2 of them, each `remOk`.
* `planOk conf rs`: what `plan` picks: one or two removals, each of a client machine `< NC` = 5 and
  `remOk`.
* `Conf`'s and `msg`'s `Pos.Countable` (the configuration channel keeps `msg`s in ghost state).

The configuration addresses carry a trivial protocol (`ConfProof.lean`'s `confProto`): nothing is
claimed about the bytes the orchestrator sends; a machine trusts only what `decode` checks.
-/
module

public import Dsverify.GeneratedProof.github_com.despreston.go_craq.examples.craqnet

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace github_com.despreston.go_craq.examples.craqnet

/-- `Conf`'s `Pos.Countable`. -/
instance Conf_countable [GooseExts] : Pos.Countable Conf :=
  .ofInjective (fun c => Pos.Countable.encode (c.N', c.Late', c.ReadTail'))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1 h2 h3; rfl)

/-- `msg`'s `Pos.Countable` (the configuration channel's values). -/
instance msg_countable [GooseExts] : Pos.Countable msg :=
  .ofInjective (fun m => Pos.Countable.encode (m.conf', m.rs'))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1 h2; rfl)

/-- A configuration `decode` accepts: a chain of 3 to `MaxChain` = 5, at most 2 late, a read
mode. -/
def confOk [GooseExts] (conf : Conf) : Prop :=
  3 ≤ uint.Z conf.N' ∧ uint.Z conf.N' ≤ 5 ∧ uint.Z conf.Late' ≤ 2 ∧ uint.Z conf.ReadTail' ≤ 1

/-- A removal `decode` accepts for `conf`: of a chain node `2..N+1`, after `1..K-1` operations. -/
def remOk [GooseExts] (conf : Conf) (r : removal) : Prop :=
  2 ≤ uint.Z r.Node' ∧ uint.Z r.Node' ≤ uint.Z conf.N' + 1 ∧ 1 ≤ uint.Z r.After' ∧
    uint.Z r.After' < 6

/-- The removals of an accepted message: at most `MaxRemovals` = 2, each `remOk`. -/
def remsOk [GooseExts] (conf : Conf) (rs : List removal) : Prop :=
  rs.length ≤ 2 ∧ ∀ r ∈ rs, remOk conf r

/-- What `plan` picks: one or two removals, each asked for by a client machine below `NC` = 5,
each `remOk`. -/
def planOk [GooseExts] (conf : Conf) (rs : List removal) : Prop :=
  1 ≤ rs.length ∧ rs.length ≤ 2 ∧ ∀ r ∈ rs, uint.Z r.Client' < 5 ∧ remOk conf r

theorem planOk_len [GooseExts] {conf : Conf} {rs : List removal} (h : planOk conf rs) :
    rs.length ≤ 2 := h.2.1

theorem remsOk_nil [GooseExts] (conf : Conf) : remsOk conf [] := by
  simp [remsOk]

end github_com.despreston.go_craq.examples.craqnet
end Perennial
