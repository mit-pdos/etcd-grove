# `pbEnc_ok`: the trusted model as a parameter

**Reviewed:** 2026-11-07, `lean` at `158829a8b9`, axiom sweep target B1-1.

- **Axiom:** `pbEnc_ok`, `Proof/google_golang_org/protobuf/proto/InvProto.lean:81`. It is quantified
  over `PbType` (`:50-68`), and `pbEnc` is opaque in `(ty, l)` (`:73`).
- **The counterexample:** branch `axiom/pbenc-inconsistent`, commit `f238daef0c`, file
  `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/pbenc/False.lean`.

## Verdict: refuted, inconsistent

`pbEnc_ok` proves `False` in Lean with no hypothesis. By the `axiom` skill's rule for an
inconsistent axiom, the axiom refutes itself: the "program" is any `panic("unreachable")`, proved
not to panic by `False.elim`.

**The claim that is false.** The axiom says that, for every record `T`, the encoding of a `*T.ty`
at `l` is a `T.wire` encoding of any `m` with `T.ro l m`. But the record is chosen by the caller,
and its premise is the record's own field. Nothing ties `T.wire` or `T.ro` to Go's protobuf
encoding.

**The attacks.** All three are in the file above. `#print axioms` of each is `[propext,
Classical.choice, Quot.sound, Perennial.EtcdGrove.pbEnc_ok]`.

1. `pbEnc_ok_false`: a record with `ro := True`, `marshals := True` and `wire := False`.
2. `pbEnc_ok_disagree`: two records of one Go type, with `wire m bs := (bs = []) = b` for
   `b = true` and for `b = false`. `pbEnc T.ty l` is the same list for both.
3. `pbEnc_ok_closed_false`: attack 1 at `Iris.BundledGFunctors.default` and the default Go type.
   It is a closed `False`.

**What rests on it.** 40 exported results, 17 of them `*_safe`, are vacuous until the fix:
every closed result through the server. The list is in `notes/pbenc-ok-inconsistent.md`.

**The proposed restatement, which the user has decided on (via etcd-grove-82, 2026-11-07).**

- State the axioms per type, at the concrete trusted instances.
- Make each wire model a fixed definition, with a satisfiability lemma.
- Add a fail-closed gate against axioms quantified over a user-buildable model record.

This is its own stage. The restated axioms get attacked before the Freeze.

**The sibling specs** `proto.{Marshal,Size,Unmarshal,Clone,MarshalAppend}Pb`: they are refuted as well (2026-11-07, branch `axiom/pbtype-specs`, `0f1f10d1d1`, `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/pbtype/False.lean`): with a record whose `wire` and `eqv` are false, `Marshal`/`Size`/`Clone`/`MarshalAppend` of a `*T` get `WP … {{ Φ }}` for every `Φ`; with `wire` true, `Unmarshal(b, nil)` returns `nil` for any bytes, so `if proto.Unmarshal([]byte{0xff}, &Entry{}) != nil { panic }` is proved safe. A contradiction with Go, not a closed `False` (that needs an adequacy theorem); `#print axioms` of each: Lean's three plus that one spec. They join the fix. grpc's `ProtoMsg` axioms are being checked in the sweep.
