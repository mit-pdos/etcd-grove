/-
`wp_auto` is disabled in this development (branch `no-wp-auto`, an experiment: do
AI-written proofs still benefit from `wp_auto`, or is spelling out every step
just as good?). Every proof module imports this one (through `Raft/Base.lean`).

* An explicit `wp_auto` is an error: write the steps (`wp_pures`, `wp_load`,
  `wp_store`, `wp_alloc x_ptr as x`, `wp_call`, `wp_func_lits`, `iclear ..` for the
  points-to facts of dead locals).
* The `wp_auto` that `wp_apply`, `wp_if_destruct`, `wp_for`, `wp_for_post` and
  `wp_join ... as` run at the end (as `try wp_auto` / `try wp_auto_lc 0`) does
  nothing: `wp_apply lem as pats` is `wp_apply +noauto lem as pats`, and
  `wp_if_destruct` only takes the pure steps of the branch condition (`wp_pures`).
* `wp_auto_lc n` (`wp_apply (lc := n)`) is not supported.

`etc/check-no-wp-auto.sh` checks that no proof mentions `wp_auto`.
-/
import Perennial.Golang.Theory.Auto

namespace Perennial
namespace NoWpAuto
open Lean Elab Tactic

macro_rules
  | `(tactic| wp_auto) => Macro.throwError
    "wp_auto is disabled in this development: spell out the steps (wp_pures, wp_load, \
      wp_store, wp_alloc x_ptr as x, iclear ..); see EtcdGrove/NoWpAuto.lean"

/-- The `try wp_auto_lc 0` at the end of `wp_apply` does nothing; asking for later
credits (`wp_apply (lc := n)`) is an error. -/
elab_rules : tactic
  | `(tactic| wp_auto_lc $n:num) => do
    if n.getNat != 0 then
      throwError "wp_auto_lc is disabled in this development (see EtcdGrove/NoWpAuto.lean)"

end NoWpAuto
end Perennial
